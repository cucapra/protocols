use std::collections::VecDeque;

use baa::BitVecOps;
use patronus::expr::{
    Context, Expr, ExprRef, ForEachChild, Simplifier, SparseExprMap, TypeCheck, find_symbols, simple_transform_expr
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type};
use crate::ir::driver_to_monitor::MonitorAutomaton;
use crate::ir::known_bit::{KnownBits, KnownBitsEvaluator};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};

// TODO: This implementation should be the basis for *universal* knownness analysis and register simplification pass

pub type KnownnessFacts = FxHashMap<SymbolId, KnownBits>;

#[derive(Debug, Clone)]
pub struct KnownnessAnalysis {
    /// Node-entry facts, keyed by physical knownness register within each node.
    pub node_entry: FxHashMap<NodeId, KnownnessFacts>,
}

/// Propagate mask-bit possibilities to a fixed point, including entry backedges.This is very similar to the analysis for fork, reaching defintions.
pub fn analyze_knownness(ctx: &Context, monitor: &MonitorAutomaton) -> KnownnessAnalysis {
    let graph = &monitor.graph;
    let initial: KnownnessFacts = monitor
        .knownness_registers
        .values()
        .map(|&register| {
            let init = monitor.register_inits[&register];
            let value = KnownBitsEvaluator::new(ctx, FxHashMap::default()).eval(init);
            (register, value)
        })
        .collect();
    // None means no incoming execution has been propagated yet.
    let mut node_entry = graph
        .nodes()
        .map(|(id, _)| (id, None))
        .collect::<FxHashMap<_, _>>();
    node_entry.insert(graph.entry, Some(initial));
    let mut pending = VecDeque::from([graph.entry]);
    while let Some(node) = pending.pop_front() {
        let entry = node_entry[&node].as_ref().unwrap().clone();
        for edge in &graph[node].transitions {
            let expr_facts = expression_facts(graph, &entry);
            let mut eval = KnownBitsEvaluator::new(ctx, expr_facts);
            if eval
                .eval(edge.guard)
                .constant()
                .is_some_and(|c| c.is_false())
            {
                continue;
            }
            // Taking this edge means its condition is true in this cycle.
            // Use that fact when deciding which parameter bits get learned.
            eval.assume_true(edge.guard);
            let out = transfer(graph, node, &entry, &mut eval);
            let target = node_entry.get_mut(&edge.target).unwrap();
            let joined = match target.as_ref() {
                None => out,
                Some(previous) => previous
                    .iter()
                    .map(|(&register, bits)| (register, bits.join(&out[&register])))
                    .collect(),
            };
            if target.as_ref() != Some(&joined) {
                *target = Some(joined);
                pending.push_back(edge.target);
            }
        }
    }
    let node_entry = node_entry
        .into_iter()
        .map(|(node, facts)| {
            let facts = facts.unwrap_or_else(|| {
                panic!("unreachable monitor node {node}: prune unreachable nodes before knownness analysis")
            });
            (node, facts)
        })
        .collect();
    KnownnessAnalysis { node_entry }
}

fn expression_facts(graph: &ProtoGraph, facts: &KnownnessFacts) -> FxHashMap<ExprRef, KnownBits> {
    facts
        .iter()
        .map(|(&register, bits)| (graph.symbol_expr(register).unwrap(), bits.clone()))
        .collect()
}

fn transfer(
    graph: &ProtoGraph,
    node: NodeId,
    entry: &KnownnessFacts,
    eval: &mut KnownBitsEvaluator<'_>,
) -> KnownnessFacts {
    let mut out = entry.clone();
    for action in &graph[node].actions {
        let Op::Assign(register, assignment) = &graph[action.op] else {
            continue;
        };
        let Some(held) = entry.get(register) else {
            continue;
        };
        let mut value = held.clone();
        // Nest in reverse order so the first applicable alternative wins.
        for &(guard, rhs) in assignment.concretes.iter().rev() {
            value = KnownBits::select(&eval.eval(guard), eval.eval(rhs), value);
        }
        let unknown = KnownBits::unknown(held.zero.width());
        value = KnownBits::select(&eval.eval(assignment.dont_care), unknown, value);
        out.insert(
            *register,
            KnownBits::select(&eval.eval(action.guard), value, held.clone()),
        );
    }
    out
}

/// Analyze, simplify using node-entry facts, eliminate unused physical masks,
/// and compress masks proven to have equal bits to one Boolean register.
/// Requires unreachable nodes to have been pruned, as for `analyze_knownness`.
pub fn simplify_monitor(
    ctx: &mut Context,
    mut monitor: MonitorAutomaton,
    symbols: &mut SymbolTable,
) -> MonitorAutomaton {
    let analysis = analyze_knownness(ctx, &monitor);
    let nodes = monitor.graph.nodes().map(|(id, _)| id).collect::<Vec<_>>();
    for node in nodes {
        let facts = &analysis.node_entry[&node];
        let facts = expression_facts(&monitor.graph, facts);
        rewrite_node(
            ctx,
            &mut monitor,
            node,
            &facts,
            &FxHashMap::default(),
            &FxHashMap::default(),
        );
    }
    remove_unused_masks(ctx, &mut monitor);
    compress_uniform_masks(ctx, &mut monitor, symbols);
    remove_unused_masks(ctx, &mut monitor);
    let node_map = monitor.graph.garbage_collect_unreachable(ctx);
    monitor.knownness_outputs = monitor
        .knownness_outputs
        .into_iter()
        .filter_map(|(node, outputs)| node_map.get(&node).map(|&new_node| (new_node, outputs)))
        .collect();
    monitor
}

struct Rewriter {
    facts: FxHashMap<ExprRef, KnownBits>,
    replacements: FxHashMap<ExprRef, ExprRef>,
    cache: FxHashMap<ExprRef, ExprRef>,
    simplifier: Simplifier<SparseExprMap<Option<ExprRef>>>,
}

impl Rewriter {
    fn expr(&mut self, ctx: &mut Context, expr: ExprRef) -> ExprRef {
        let mut eval = KnownBitsEvaluator::new(ctx, self.facts.clone());
        // Evaluate each original subexpression once, before borrowing ctx mutably.
        let mut pending = vec![expr];
        let mut values = FxHashMap::default();
        while let Some(e) = pending.pop() {
            if values.contains_key(&e) {
                continue;
            }
            values.insert(e, eval.eval(e));
            ctx[e].for_each_child(|child| pending.push(*child));
        }
        let result = simple_transform_expr(ctx, expr, |ctx, original, _| {
            if let Some(&replacement) = self.cache.get(&original) {
                return Some(replacement);
            }
            let replacement = if let Some(&replacement) = self.replacements.get(&original) {
                Some(replacement)
            } else if let Some(constant) = values[&original].constant() {
                Some(ctx.bv_lit(&constant))
            } else if let Some(bits) = self.facts.get(&original) {
                // Encode partially determined bits, keeping only the remaining
                // bits dynamic. This is a single substitution, not a recurrence.
                if bits.zero.is_zero() && bits.one.is_zero() {
                    None
                } else {
                    let unknown = bits.zero.or(&bits.one).not();
                    let unknown = ctx.bv_lit(&unknown);
                    let one = ctx.bv_lit(&bits.one);
                    let dynamic = ctx.and(original, unknown);
                    Some(ctx.or(dynamic, one))
                }
            } else {
                None
            };
            if let Some(replacement) = replacement {
                self.cache.insert(original, replacement);
            }
            replacement
        });
        self.simplifier.simplify(ctx, result)
    }
}

fn rewrite_node(
    ctx: &mut Context,
    monitor: &mut MonitorAutomaton,
    node: NodeId,
    facts: &FxHashMap<ExprRef, KnownBits>,
    replacements: &FxHashMap<ExprRef, ExprRef>,
    targets: &FxHashMap<SymbolId, SymbolId>,
) {
    let mut rewrite = Rewriter {
        facts: facts.clone(),
        replacements: replacements.clone(),
        cache: FxHashMap::default(),
        simplifier: Simplifier::new(SparseExprMap::default()),
    };
    let graph = &mut monitor.graph;
    let mut actions = Vec::new();
    for action in graph[node].actions.clone() {
        let guard = rewrite.expr(ctx, action.guard);
        if guard == ctx.get_false() {
            continue;
        }
        let op = match graph[action.op].clone() {
            Op::Assign(register, assignment) => {
                let target = targets.get(&register).copied().unwrap_or(register);
                let dont_care = rewrite.expr(ctx, assignment.dont_care);
                let concretes = assignment
                    .concretes
                    .into_iter()
                    .filter_map(|(g, rhs)| {
                        let g = rewrite.expr(ctx, g);
                        if g == ctx.get_false() {
                            return None;
                        }
                        let mut rhs = rewrite.expr(ctx, rhs);
                        if target != register {
                            // Compression proved all bits equal; one bit is the
                            // update for the replacement Boolean register.
                            let bit = ctx.slice(rhs, 0, 0);
                            rhs = rewrite.simplifier.simplify(ctx, bit);
                        }
                        Some((g, rhs))
                    })
                    .collect::<Vec<_>>();
                let held = graph
                    .symbol_expr(target)
                    .map(|held| rewrite.expr(ctx, held));
                if dont_care == ctx.get_false()
                    && concretes.iter().all(|(_, rhs)| Some(*rhs) == held)
                {
                    continue;
                }
                Op::Assign(
                    target,
                    Assignment {
                        dont_care,
                        concretes,
                    },
                )
            }
            Op::AssertEq(lhs, rhs) => {
                let lhs = rewrite.expr(ctx, lhs);
                let rhs = rewrite.expr(ctx, rhs);
                let (lhs, rhs) = trim_equal_padding(ctx, &mut rewrite.simplifier, lhs, rhs);
                let equal = ctx.equal(lhs, rhs);
                let equal = rewrite.simplifier.simplify(ctx, equal);
                if equal == ctx.get_true() {
                    continue;
                }
                Op::AssertEq(lhs, rhs)
            }
            op => op,
        };
        let op = graph.o(op);
        actions.push(Action::new(guard, op));
    }
    graph.node_mut(node).actions = actions;
    let mut edges = graph[node].transitions.clone();
    for edge in &mut edges {
        edge.guard = rewrite.expr(ctx, edge.guard);
    }
    edges.retain(|edge| edge.guard != ctx.get_false());
    graph.node_mut(node).transitions = edges;
    if let Some(outputs) = monitor.knownness_outputs.get_mut(&node) {
        for output in outputs.values_mut() {
            *output = rewrite.expr(ctx, *output);
        }
    }
}

/// Masked comparisons often acquire identical zero padding during ordinary
/// expression simplification. Strip equal high/low bits so a partial overlap
/// reads as e.g. `assert_eq(a[2:1], b[1:0])` rather than padded concatenations.
fn trim_equal_padding(
    ctx: &mut Context,
    simplifier: &mut Simplifier<SparseExprMap<Option<ExprRef>>>,
    lhs: ExprRef,
    rhs: ExprRef,
) -> (ExprRef, ExprRef) {
    let mut eval = KnownBitsEvaluator::new(ctx, FxHashMap::default());
    let (a, b) = (eval.eval(lhs), eval.eval(rhs));
    let equal = a.zero.and(&b.zero).or(&a.one.and(&b.one));
    let width = equal.width();
    let Some(lo) = (0..width).find(|&bit| !equal.is_bit_set(bit)) else {
        return (lhs, rhs);
    };
    let hi = (lo..width)
        .rev()
        .find(|&bit| !equal.is_bit_set(bit))
        .unwrap();
    let lhs = ctx.slice(lhs, hi, lo);
    let rhs = ctx.slice(rhs, hi, lo);
    (simplifier.simplify(ctx, lhs), simplifier.simplify(ctx, rhs))
}

fn op_reads(op: &Op) -> Vec<ExprRef> {
    match op {
        Op::Assign(_, a) => std::iter::once(a.dont_care)
            .chain(a.concretes.iter().flat_map(|&(g, rhs)| [g, rhs]))
            .collect(),
        Op::AssertEq(a, b) => vec![*a, *b],
        _ => vec![],
    }
}

fn remove_unused_masks(ctx: &Context, monitor: &mut MonitorAutomaton) {
    let graph = &mut monitor.graph;
    let masks = monitor
        .knownness_registers
        .values()
        .copied()
        .collect::<FxHashSet<_>>();
    let mut roots = monitor
        .knownness_outputs
        .values()
        .flat_map(|outputs| outputs.values().copied())
        .collect::<Vec<_>>();
    let mut definitions = FxHashMap::<SymbolId, Vec<ExprRef>>::default();
    for (_, node) in graph.nodes() {
        roots.extend(node.transitions.iter().map(|edge| edge.guard));
        for action in &node.actions {
            roots.push(action.guard);
            match &graph[action.op] {
                Op::Assign(register, _) if masks.contains(register) => {
                    definitions
                        .entry(*register)
                        .or_default()
                        .extend(op_reads(&graph[action.op]));
                }
                op => roots.extend(op_reads(op)),
            }
        }
    }
    let expr_to_mask = masks
        .iter()
        .map(|&r| (graph.symbol_expr(r).unwrap(), r))
        .collect::<FxHashMap<_, _>>();
    let mut needed = FxHashSet::default();
    while let Some(root) = roots.pop() {
        for symbol in find_symbols(ctx, root) {
            if let Some(&mask) = expr_to_mask.get(&symbol)
                && needed.insert(mask)
            {
                roots.extend(definitions.get(&mask).into_iter().flatten().copied());
            }
        }
    }
    let dead = masks.difference(&needed).copied().collect::<FxHashSet<_>>();
    let nodes = graph.nodes().map(|(id, _)| id).collect::<Vec<_>>();
    for node in nodes {
        let actions = graph[node].actions.iter().filter(|action| {
            !matches!(graph[action.op], Op::Assign(register, _) if dead.contains(&register))
        }).cloned().collect();
        graph.node_mut(node).actions = actions;
    }
    monitor
        .knownness_registers
        .retain(|_, register| !dead.contains(register));
    monitor
        .register_inits
        .retain(|register, _| !dead.contains(register));
}

/// A deliberately conservative syntactic proof. The mask may hold its previous
/// uniform value or combine uniform constants/values with bitwise ops and ITEs.
/// References to other multi-bit registers and composed partial bindings are
/// left alone, even when a stronger analysis could prove their bits equal.
fn uniform(
    ctx: &Context,
    expr: ExprRef,
    mask: Option<ExprRef>,
    cache: &mut FxHashMap<ExprRef, bool>,
) -> bool {
    if let Some(&result) = cache.get(&expr) {
        return result;
    }
    let result = if expr.get_bv_type(ctx) == Some(1) || Some(expr) == mask {
        true
    } else {
        match ctx[expr] {
            Expr::BVLiteral(value) => {
                let value = value.get(ctx);
                value.is_zero() || value.is_all_ones()
            }
            Expr::BVNot(e, _) | Expr::BVSlice { e, .. } | Expr::BVSignExt { e, .. } => {
                uniform(ctx, e, mask, cache)
            }
            Expr::BVAnd(a, b, _) | Expr::BVOr(a, b, _) | Expr::BVXor(a, b, _) => {
                uniform(ctx, a, mask, cache) && uniform(ctx, b, mask, cache)
            }
            Expr::BVIte { tru, fals, .. } => {
                uniform(ctx, tru, mask, cache) && uniform(ctx, fals, mask, cache)
            }
            _ => false,
        }
    };
    cache.insert(expr, result);
    result
}

fn compress_uniform_masks(
    ctx: &mut Context,
    monitor: &mut MonitorAutomaton,
    symbols: &mut SymbolTable,
) {
    let graph = &mut monitor.graph;
    let mut replacements = FxHashMap::default();
    let mut targets = FxHashMap::default();
    for argument in graph.args.clone() {
        let Some(&old) = monitor.knownness_registers.get(&argument.symbol()) else {
            continue;
        };
        let old_expr = graph.symbol_expr(old).unwrap();
        let width = old_expr.get_bv_type(ctx).unwrap();
        let init = monitor.register_inits[&old];
        if width == 1 || !uniform(ctx, init, None, &mut FxHashMap::default()) {
            continue;
        }
        // Induction for this mask alone: initialization is uniform, and each
        // update is uniform assuming the previous value of this mask is uniform.
        let mut cache = FxHashMap::default();
        let uniform_updates = graph.nodes().all(|(_, node)| {
            node.actions.iter().all(|action| match &graph[action.op] {
                Op::Assign(target, assignment) if *target == old => {
                    assignment.dont_care == ctx.get_false()
                        && assignment
                            .concretes
                            .iter()
                            .all(|&(_, rhs)| uniform(ctx, rhs, Some(old_expr), &mut cache))
                }
                _ => true,
            })
        });
        if !uniform_updates {
            continue;
        }

        let base = format!("{}_bool", symbols[old].name());
        let mut name = base.clone();
        let mut suffix = 1;
        while symbols.symbol_id_from_name_in_active_scope(&name).is_some() {
            name = format!("{base}_{suffix}");
            suffix += 1;
        }
        let register =
            symbols.add_without_parent(name, Type::BitVec(1), SymbolKind::AutomatonState);
        let expr = ctx.bv_symbol(&symbols[register].full_name(symbols), 1);
        graph.cache_symbol_expr(register, expr);
        let zero = ctx.zero(width);
        let ones = ctx.ones(width);
        replacements.insert(old_expr, ctx.ite(expr, ones, zero));
        monitor.register_inits.remove(&old);
        let init = ctx.slice(init, 0, 0);
        let init = graph.simplifier.simplify(ctx, init);
        monitor.register_inits.insert(register, init);
        monitor
            .knownness_registers
            .insert(argument.symbol(), register);
        targets.insert(old, register);
    }
    if targets.is_empty() {
        return;
    }
    let nodes = graph.nodes().map(|(id, _)| id).collect::<Vec<_>>();
    for node in nodes {
        rewrite_node(
            ctx,
            monitor,
            node,
            &FxHashMap::default(),
            &replacements,
            &targets,
        );
    }
}

#[cfg(test)]
mod tests;
