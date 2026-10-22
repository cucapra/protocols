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

/// Register updates must not assign X; DUT pin assignments may still do so.
/// Within-cycle reads must already be resolved by contraction (or constructed
/// directly as composed expressions). Remaining register reads mean node entry.
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

fn region(ctx: &Context, graph: &ProtoGraph, entry: NodeId) -> FxHashSet<NodeId> {
    let mut nodes = FxHashSet::default();
    let mut pending = vec![entry];
    while let Some(node) = pending.pop() {
        if nodes.insert(node) {
            pending.extend(
                graph[node]
                    .transitions
                    .iter()
                    .filter(|e| e.guard != ctx.get_false())
                    .map(|e| e.target),
            );
        }
    }
    nodes
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

/// Substitute proven incoming values and remove state without observable readers.
/// `preserved` identifies physical registers read externally.
/// Nodes outside `entry`'s region, including their reads and writes, are preserved.
/// The returned IDs are unused within this region. Their cached expressions stay
/// available for other entry points into the graph.
pub fn rewrite_registers(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    entry: NodeId,
    analysis: &RegisterAnalysis,
    preserved: &FxHashSet<SymbolId>,
) -> FxHashSet<SymbolId> {
    let nodes = region(ctx, graph, entry);
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
        // Contraction (or the producer of already-composed expressions) resolved
        // within-cycle updates. Every remaining register read means node entry.
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
        graph.node_mut(node).actions = actions;
        let mut edges = graph[node].transitions.clone();
        for edge in &mut edges {
            edge.guard = simplify(ctx, &mut simplifier, edge.guard, &replacements);
        }
        edges.retain(|e| e.guard != ctx.get_false());
        graph.node_mut(node).transitions = edges;
    }

    // Rewriting edge guards can make more nodes unreachable. Their actions stay
    // untouched and must not keep registers alive in this region.
    let nodes = region(ctx, graph, entry);
    let mut roots = Vec::new();
    let mut definitions = FxHashMap::<SymbolId, Vec<ExprRef>>::default();
    let mut needed = preserved.clone();
    for &id in &nodes {
        let node = &graph[id];
        roots.extend(node.transitions.iter().map(|e| e.guard));
        for action in &node.actions {
            match &graph[action.op] {
                Op::Assign(r, _) if symbols[*r].kind() == SymbolKind::AutomatonState => {
                    let dependencies = definitions.entry(*r).or_default();
                    dependencies.push(action.guard);
                    dependencies.extend(reads(&graph[action.op]));
                }
                op => {
                    roots.push(action.guard);
                    roots.extend(reads(op));
                }
            }
        }
    }
    for r in &needed {
        roots.extend(definitions.get(r).into_iter().flatten().copied());
    }
    while let Some(root) = roots.pop() {
        for symbol in find_symbols(ctx, root) {
            if let Some(&r) = expr_to_register.get(&symbol)
                && needed.insert(r)
            {
                roots.extend(definitions.get(&r).into_iter().flatten().copied());
            }
        }
    }
    let dead = expr_to_register
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

/// Analyze and rewrite one reachable region. Callers own initialization and
/// register metadata and remove the returned register IDs from those maps.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::{ROOT_SCOPE, SymbolKind, SymbolTable, Type};
    use crate::ir::proto_graph::{Action, Node, Transition};

    fn fixture() -> (Context, ProtoGraph, SymbolTable, SymbolId) {
        fixture_width(8)
    }

    fn fixture_width(width: u32) -> (Context, ProtoGraph, SymbolTable, SymbolId) {
        let mut ctx = Context::default();
        let mut symbols = SymbolTable::default();
        let r =
            symbols.add_without_parent("r".into(), Type::BitVec(width), SymbolKind::AutomatonState);
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        graph.cache_symbol_expr(r, ctx.bv_symbol("r", width));
        (ctx, graph, symbols, r)
    }

    fn assign(ctx: &Context, graph: &mut ProtoGraph, node: NodeId, r: SymbolId, value: ExprRef) {
        let op = graph.o(Op::Assign(
            r,
            Assignment::concrete(ctx.get_false(), ctx.get_true(), value),
        ));
        graph.push_action(node, Action::new(ctx.get_true(), op));
    }

    #[test]
    fn checks_and_edges_keep_the_updates_resolved_by_contraction() {
        let (mut ctx, mut g, symbols, r) = fixture();
        let entry = g.entry;
        let end = g.n(Node::empty());
        let current = g.symbol_expr(r).unwrap();
        let zero = ctx.zero(8);
        let one = ctx.one(8);
        let incremented = ctx.add(current, one);
        assign(&ctx, &mut g, entry, r, incremented);
        let check = g.o(Op::AssertEq(current, one));
        g.push_action(entry, Action::new(ctx.get_true(), check));
        let mismatch = g.o(Op::AssertEq(current, zero));
        g.push_action(entry, Action::new(ctx.get_true(), mismatch));
        let updated = ctx.equal(current, one);
        g.push_transition(entry, Transition::new(updated, end, true));
        let end_check = g.o(Op::AssertEq(current, one));
        g.push_action(end, Action::new(ctx.get_true(), end_check));
        crate::ir::edge_contract::contract_edges(&mut ctx, &mut g, &symbols);
        let dead = simplify_registers(
            &mut ctx,
            &mut g,
            &symbols,
            entry,
            &RegisterFacts::from_iter([(r, zero)]),
            &FxHashSet::default(),
        );
        assert!(g[end].actions.is_empty());
        assert_eq!(g[entry].transitions[0].guard, ctx.get_true());
        assert_eq!(g[entry].actions.len(), 1);
        assert_eq!(g[g[entry].actions[0].op], Op::AssertEq(one, zero));
        assert!(dead.contains(&r));
    }

    #[test]
    fn subgraph_rewrite_preserves_external_reads_and_writes() {
        let (mut ctx, mut g, symbols, r) = fixture();
        let outside = g.entry;
        let entry = g.n(Node::empty());
        let current = g.symbol_expr(r).unwrap();
        let zero = ctx.zero(8);
        assign(&ctx, &mut g, outside, r, zero);
        let check = g.o(Op::AssertEq(current, zero));
        g.push_action(outside, Action::new(ctx.get_true(), check));
        let outside_node_with_check = g[outside].clone();
        let one = ctx.one(8);
        assign(&ctx, &mut g, entry, r, one);
        let dead = simplify_registers(
            &mut ctx,
            &mut g,
            &symbols,
            entry,
            &RegisterFacts::from_iter([(r, zero)]),
            &FxHashSet::default(),
        );
        assert!(dead.contains(&r));
        assert!(g[entry].actions.is_empty());
        assert_eq!(g[outside], outside_node_with_check);
        assert_eq!(g.symbol_expr(r), Some(current));
    }

    #[test]
    fn nodes_without_analysis_facts_stay_untouched_after_their_edge_is_removed() {
        let (mut ctx, mut g, symbols, r) = fixture_width(1);
        let entry = g.entry;
        let blocked = g.n(Node::empty());
        let descendant = g.n(Node::empty());
        let end = g.n(Node::empty());
        let current = g.symbol_expr(r).unwrap();
        let not_current = ctx.not(current);
        g.push_transition(entry, Transition::new(current, blocked, true));
        g.push_transition(entry, Transition::new(not_current, end, true));
        g.push_transition(blocked, Transition::new(ctx.get_true(), descendant, true));
        let check = g.o(Op::AssertEq(current, ctx.get_true()));
        g.push_action(blocked, Action::new(ctx.get_true(), check));
        g.push_action(descendant, Action::new(ctx.get_true(), check));
        let original_blocked = g[blocked].clone();
        let original_descendant = g[descendant].clone();
        let initial = RegisterFacts::from_iter([(r, ctx.get_false())]);
        let analysis = analyze_registers(&mut ctx, &g, &symbols, entry, &initial);
        assert_eq!(analysis[&blocked], None);
        assert!(!analysis.contains_key(&descendant));
        let dead = rewrite_registers(
            &mut ctx,
            &mut g,
            &symbols,
            entry,
            &analysis,
            &FxHashSet::default(),
        );
        assert!(dead.contains(&r));
        assert_eq!(g[entry].transitions.len(), 1);
        assert_eq!(g[entry].transitions[0].target, end);
        assert_eq!(g[blocked], original_blocked);
        assert_eq!(g[descendant], original_descendant);
    }

    #[test]
    fn dead_register_cycles_have_no_observable_roots() {
        let (mut ctx, mut g, mut symbols, r) = fixture();
        let s = symbols.add_without_parent("s".into(), Type::BitVec(8), SymbolKind::AutomatonState);
        let s_expr = ctx.bv_symbol("s", 8);
        g.cache_symbol_expr(s, s_expr);
        let r_expr = g.symbol_expr(r).unwrap();
        let entry = g.entry;
        assign(&ctx, &mut g, entry, r, s_expr);
        assign(&ctx, &mut g, entry, s, r_expr);
        let dead = simplify_registers(
            &mut ctx,
            &mut g,
            &symbols,
            entry,
            &RegisterFacts::default(),
            &FxHashSet::default(),
        );
        assert_eq!(dead.len(), 2);
        assert!(g[entry].actions.is_empty());
    }

    #[test]
    fn first_concrete_alternative_wins() {
        let (mut ctx, mut g, symbols, r) = fixture();
        let end = g.n(Node::empty());
        let one = ctx.one(8);
        let two = ctx.bit_vec_val(2, 8);
        let op = g.o(Op::Assign(
            r,
            Assignment {
                dont_care: ctx.get_false(),
                concretes: vec![(ctx.get_true(), one), (ctx.get_true(), two)],
            },
        ));
        g.push_action(g.entry, Action::new(ctx.get_true(), op));
        g.push_transition(g.entry, Transition::new(ctx.get_true(), end, true));
        let facts = analyze_registers(&mut ctx, &g, &symbols, g.entry, &RegisterFacts::default());
        assert_eq!(facts[&end].as_ref().unwrap().get(&r), Some(&one));
    }

    #[test]
    fn symbolic_values_above_64_bits_are_propagated_whole() {
        let (mut ctx, mut g, mut symbols, r) = fixture_width(128);
        let parameter_id = symbols.add_without_parent(
            "wide_parameter".into(),
            Type::BitVec(128),
            SymbolKind::Arg(0),
        );
        let parameter = ctx.bv_symbol("wide_parameter", 128);
        g.cache_symbol_expr(parameter_id, parameter);
        let ones = ctx.ones(128);
        let value = ctx.and(parameter, ones);
        let entry = g.entry;
        assign(&ctx, &mut g, entry, r, value);
        let end = g.n(Node::empty());
        g.push_transition(entry, Transition::new(ctx.get_true(), end, true));
        let facts = analyze_registers(&mut ctx, &g, &symbols, entry, &RegisterFacts::default());
        assert_eq!(facts[&end].as_ref().unwrap().get(&r), Some(&parameter));
    }
}
