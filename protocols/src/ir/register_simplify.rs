use std::collections::VecDeque;

use patronus::expr::{Context, Expr, ExprRef, Simplifier, SparseExprMap, find_symbols};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph, remap_expr};

pub type RegisterFacts = FxHashMap<SymbolId, ExprRef>;
pub type RegisterAnalysis = FxHashMap<NodeId, Option<RegisterFacts>>;
type ExprSimplifier = Simplifier<SparseExprMap<Option<ExprRef>>>;

/// Simplify using replacement expressions (which are hopefully simpler), then use
/// the Patronus simpler
fn simplify(
    ctx: &mut Context,
    simplifier: &mut ExprSimplifier,
    expr: ExprRef,
    replacements: &FxHashMap<ExprRef, ExprRef>,
) -> ExprRef {
    let expr = remap_expr(ctx, expr, replacements);
    simplifier.simplify(ctx, expr)
}

// Very annoying step we have to do to go from RegisterFacts, which operates over symbols
// to expressions, which we can then sub in to simplify expressions
fn register_facts_to_exprs(
    graph: &ProtoGraph,
    facts: &RegisterFacts,
) -> FxHashMap<ExprRef, ExprRef> {
    facts
        .iter()
        .map(|(&r, &v)| (graph.symbol_expr(r).unwrap(), v))
        .collect()
}

/// Constants and arguments are guaranteed immutable, so we only guarantee
/// an expression is immutable if it is made up of those.
fn is_immutable(
    ctx: &Context,
    expr: ExprRef,
    symbol_ids: &FxHashMap<ExprRef, SymbolId>,
    symbols: &SymbolTable,
) -> bool {
    find_symbols(ctx, expr)
        .into_iter()
        .all(|s| symbol_ids.get(&s).is_some_and(|id| symbols[*id].is_arg()))
}

/// For every AutomatonState in this node, provide a mapping to the expression
/// it takes on in this node (if its assigned a new value)
fn updates(
    ctx: &mut Context,
    graph: &ProtoGraph,
    symbols: &SymbolTable,
    node: NodeId,
) -> FxHashMap<ExprRef, ExprRef> {
    let mut updates = FxHashMap::default();
    for action in &graph[node].actions {
        if let Op::Assign(register, assignment) = &graph[action.op]
            && symbols[*register].kind() == SymbolKind::AutomatonState
        {
            assert_eq!(
                assignment.dont_care,
                ctx.get_false(),
                "generated register updates must not assign X"
            );
            let held = graph.symbol_expr(*register).unwrap();
            let mut value = held;
            for &(guard, rhs) in assignment.concretes.iter().rev() {
                value = ctx.ite(guard, rhs, value);
            }
            let value = ctx.ite(action.guard, value, held);
            assert!(
                updates.insert(held, value).is_none(),
                "multiple updates for {register} at {node}"
            );
        }
    }
    updates
}

// recursively find simple versions of expressions based on an assumed value of the
// top-level expression, return a map from expressions to their simplified versions
fn assume(ctx: &Context, expr: ExprRef, assumed_value: bool) -> FxHashMap<ExprRef, ExprRef> {
    let mut assumptions = FxHashMap::default();
    assume_helper(ctx, expr, assumed_value, &mut assumptions);

    assumptions
}

fn assume_helper(
    ctx: &Context,
    expr: ExprRef,
    assumed_value: bool,
    facts: &mut FxHashMap<ExprRef, ExprRef>,
) {
    facts.insert(
        expr,
        if assumed_value {
            ctx.get_true()
        } else {
            ctx.get_false()
        },
    );
    match ctx[expr] {
        Expr::BVNot(e, _) => assume_helper(ctx, e, !assumed_value, facts),
        Expr::BVAnd(a, b, _) if assumed_value => {
            assume_helper(ctx, a, true, facts);
            assume_helper(ctx, b, true, facts);
        }
        Expr::BVOr(a, b, _) if !assumed_value => {
            assume_helper(ctx, a, false, facts);
            assume_helper(ctx, b, false, facts);
        }
        _ => {}
    }
}

pub fn analyze_registers(
    ctx: &mut Context,
    graph: &ProtoGraph,
    symbols: &SymbolTable,
    entry: NodeId,
    initial: &RegisterFacts,
) -> RegisterAnalysis {
    let mut simplifier = ExprSimplifier::new(SparseExprMap::default());
    let registers = graph
        .symbol_expr
        .keys()
        .copied()
        .filter(|r| symbols[*r].kind() == SymbolKind::AutomatonState)
        .collect::<Vec<_>>();
    let symbol_ids = graph
        .symbol_expr
        .iter()
        .map(|(&id, &expr)| (expr, id))
        .collect();

    // Boundary facts: keep only entry values that can be reused across cycles.
    let initial = initial
        .iter()
        .filter_map(|(&r, &value)| {
            assert_eq!(symbols[r].kind(), SymbolKind::AutomatonState);
            let value = simplifier.simplify(ctx, value);
            is_immutable(ctx, value, &symbol_ids, symbols).then_some((r, value))
        })
        .collect();

    // For a given node BEFORE it has run, Some(register_face) means
    // that node is reachable, and we have an exact expression for each
    // present register. An absent register has unknown value.
    // None means no we haven't reached this node (yet).
    let mut facts: FxHashMap<NodeId, Option<RegisterFacts>> =
        FxHashMap::from_iter([(entry, Some(initial))]);

    // Standard worklist for dataflow analysis; start at entry, and
    // revisit a successor whenever its merged facts change.
    let mut pending = VecDeque::from([entry]);
    while let Some(node) = pending.pop_front() {
        let replacements = register_facts_to_exprs(graph, facts[&node].as_ref().unwrap());

        // Compute the updated values of every register once this node executes
        let updates = updates(ctx, graph, symbols, node);
        for edge in &graph[node].transitions {
            // Contraction already resolved the actions into the edge condition.
            // Only substitute entry facts here; applying updates again is wrong.
            let guard = simplify(ctx, &mut simplifier, edge.guard, &replacements);
            facts.entry(edge.target).or_insert(None);
            if guard == ctx.get_false() {
                continue;
            }
            let assumptions = assume(ctx, guard, true);

            // Transfer function: First substitute the entry values into each update.
            // Next, we know the edge must be true so we simplify under the edge condition.
            // Finally, we keep the resulting expressions iff immutable.
            let out: RegisterFacts = registers
                .iter()
                .filter_map(|&register| {
                    let current = graph.symbol_expr(register).unwrap();
                    let value = updates.get(&current).copied().unwrap_or(current);
                    let value = simplify(ctx, &mut simplifier, value, &replacements);
                    let value = simplify(ctx, &mut simplifier, value, &assumptions);
                    is_immutable(ctx, value, &symbol_ids, symbols).then_some((register, value))
                })
                .collect();

            // Merge: combine this edge with the target node's other in-edges.
            // If this is the first processed edge, use its facts; otherwise, reconcile
            // it with existing facts by only keeping a fact if it is identical between all branches.
            let target = facts.get_mut(&edge.target).unwrap();
            let joined = match target.as_ref() {
                None => out,
                Some(old) => old
                    .iter()
                    .filter_map(|(&r, &v)| (out.get(&r) == Some(&v)).then_some((r, v)))
                    .collect(),
            };

            // add back to the worklist if changed
            if target.as_ref() != Some(&joined) {
                *target = Some(joined);
                pending.push_back(edge.target);
            }
        }
    }
    facts
}

fn reads(op: &Op) -> Vec<ExprRef> {
    match op {
        Op::Assign(_, a) => std::iter::once(a.dont_care)
            .chain(a.concretes.iter().flat_map(|&(g, v)| [g, v]))
            .collect(),
        Op::AssertEq(a, b) => vec![*a, *b],
        _ => vec![],
    }
}

/// Given a `RegisterAnalysis`, substitute in the statically known values in the place
/// of the registers for all nodes reachable from `entry`.
/// After, if a register is never read, we remove it and add it to the the return `FxHashSet`.
/// `preserved` are registers that we won't remove even if unused.
pub fn rewrite_registers(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    entry: NodeId,
    analysis: &RegisterAnalysis,
    preserved: &FxHashSet<SymbolId>,
) -> FxHashSet<SymbolId> {
    let nodes = graph.reachable_node_ids(ctx, entry);
    let expr_to_register = graph
        .symbol_expr
        .iter()
        .filter(|(r, _)| symbols[**r].kind() == SymbolKind::AutomatonState)
        .map(|(&r, &expr)| (expr, r))
        .collect::<FxHashMap<_, _>>();
    let mut simplifier = ExprSimplifier::new(SparseExprMap::default());
    for &node in &nodes {
        let Some(facts) = analysis.get(&node).and_then(Option::as_ref) else {
            continue;
        };
        let replacements = register_facts_to_exprs(graph, facts);

        // Generate new versions of the actions using the replacements.
        let mut actions = Vec::new();
        for action in graph[node].actions.clone() {
            let guard = simplify(ctx, &mut simplifier, action.guard, &replacements);
            if guard == ctx.get_false() {
                continue;
            }
            let op = match graph[action.op].clone() {
                Op::Assign(target, a) => {
                    let dont_care = simplify(ctx, &mut simplifier, a.dont_care, &replacements);
                    let concretes = if dont_care == ctx.get_true() {
                        vec![]
                    } else {
                        a.concretes
                            .into_iter()
                            .filter_map(|(g, rhs)| {
                                let g = simplify(ctx, &mut simplifier, g, &replacements);
                                if g == ctx.get_false() {
                                    return None;
                                }
                                Some((g, simplify(ctx, &mut simplifier, rhs, &replacements)))
                            })
                            .collect::<Vec<_>>()
                    };
                    if symbols[target].kind() == SymbolKind::AutomatonState
                        && dont_care == ctx.get_false()
                    {
                        let held = simplify(
                            ctx,
                            &mut simplifier,
                            graph.symbol_expr(target).unwrap(),
                            &replacements,
                        );
                        if concretes.iter().all(|&(_, rhs)| rhs == held) {
                            continue;
                        }
                    }
                    Op::Assign(
                        target,
                        Assignment {
                            dont_care,
                            concretes,
                        },
                    )
                }
                Op::AssertEq(a, b) => {
                    let a = simplify(ctx, &mut simplifier, a, &replacements);
                    let b = simplify(ctx, &mut simplifier, b, &replacements);
                    let equal = ctx.equal(a, b);
                    let equal = simplifier.simplify(ctx, equal);
                    if equal == ctx.get_true() {
                        continue;
                    }
                    match ctx[equal] {
                        Expr::BVEqual(a, b) => Op::AssertEq(a, b),
                        _ => Op::AssertEq(a, b),
                    }
                }
                op => op,
            };
            let op = if op == graph[action.op] {
                action.op
            } else {
                graph.o(op)
            };
            actions.push(Action::new(guard, op));
        }

        // rebuild the node with the new actions, and simplify transitions as well.
        graph.node_mut(node).actions = actions;
        let mut edges = graph[node].transitions.clone();
        for edge in &mut edges {
            edge.guard = simplify(ctx, &mut simplifier, edge.guard, &replacements);
        }
        edges.retain(|e| e.guard != ctx.get_false());
        graph.node_mut(node).transitions = edges;
    }

    // work through used expressions to find all the used registers
    let nodes = graph.reachable_node_ids(ctx, entry);
    let mut worklist = Vec::new();
    let mut definitions = FxHashMap::<SymbolId, Vec<ExprRef>>::default();
    let mut needed = preserved.clone();
    for &id in &nodes {
        let node = &graph[id];
        worklist.extend(node.transitions.iter().map(|e| e.guard));
        for action in &node.actions {
            match &graph[action.op] {
                Op::Assign(r, _) if symbols[*r].kind() == SymbolKind::AutomatonState => {
                    let dependencies = definitions.entry(*r).or_default();
                    dependencies.push(action.guard);
                    dependencies.extend(reads(&graph[action.op]));
                }
                op => {
                    worklist.push(action.guard);
                    worklist.extend(reads(op));
                }
            }
        }
    }

    for r in &needed {
        worklist.extend(definitions.get(r).into_iter().flatten().copied());
    }
    while let Some(root) = worklist.pop() {
        for symbol in find_symbols(ctx, root) {
            if let Some(&r) = expr_to_register.get(&symbol)
                && needed.insert(r)
            {
                worklist.extend(definitions.get(&r).into_iter().flatten().copied());
            }
        }
    }

    // find all the dead register symbols, remove their assignment actions, return that set
    let dead: FxHashSet<SymbolId> = expr_to_register
        .values()
        .filter(|r| !needed.contains(r))
        .copied()
        .collect::<FxHashSet<_>>();
    for node in nodes {
        let actions = graph[node]
            .actions
            .iter()
            .filter(|a| !matches!(graph[a.op], Op::Assign(r, _) if dead.contains(&r)))
            .cloned()
            .collect();
        graph.node_mut(node).actions = actions;
    }
    dead
}

pub fn simplify_registers(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    entry: NodeId,
    initial: &RegisterFacts,
    preserved: &FxHashSet<SymbolId>,
) -> FxHashSet<SymbolId> {
    let analysis = analyze_registers(ctx, graph, symbols, entry, initial);
    rewrite_registers(ctx, graph, symbols, entry, &analysis, preserved)
}
