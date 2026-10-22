use std::collections::VecDeque;

use patronus::expr::{Context, Expr, ExprRef, Simplifier, SparseExprMap, find_symbols};
use rustc_hash::FxHashMap;

use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph, remap_expr};

pub type RegisterFacts = FxHashMap<SymbolId, ExprRef>;
pub type RegisterAnalysis = FxHashMap<NodeId, Option<RegisterFacts>>;
type ExprSimplifier = Simplifier<SparseExprMap<Option<ExprRef>>>;

fn simplify(
    ctx: &mut Context,
    simplifier: &mut ExprSimplifier,
    expr: ExprRef,
    replacements: &FxHashMap<ExprRef, ExprRef>,
) -> ExprRef {
    let expr = remap_expr(ctx, expr, replacements);
    simplifier.simplify(ctx, expr)
}

fn expression_facts(graph: &ProtoGraph, facts: &RegisterFacts) -> FxHashMap<ExprRef, ExprRef> {
    facts
        .iter()
        .map(|(&r, &v)| (graph.symbol_expr(r).unwrap(), v))
        .collect()
}

// Constants and transaction arguments are stable between visits. Ports, loop
// values, unresolved registers, and uncached symbols (including X) are not.
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

// Only whole Boolean expressions are assumed, never individual bit-vector bits.
fn assume(ctx: &Context, expr: ExprRef, value: bool, facts: &mut FxHashMap<ExprRef, ExprRef>) {
    facts.insert(
        expr,
        if value {
            ctx.get_true()
        } else {
            ctx.get_false()
        },
    );
    match ctx[expr] {
        Expr::BVNot(e, _) => assume(ctx, e, !value, facts),
        Expr::BVAnd(a, b, _) if value => {
            assume(ctx, a, true, facts);
            assume(ctx, b, true, facts);
        }
        Expr::BVOr(a, b, _) if !value => {
            assume(ctx, a, false, facts);
            assume(ctx, b, false, facts);
        }
        _ => {}
    }
}

/// Propagate whole register values starting at `entry`.
///
/// `initial` describes arrivals at this entry, not necessarily the graph's global
/// initialization. Other predecessors outside this reachable region are ignored.
/// Symbol kinds identify register state and which values can safely be propagated.
/// Joins retain identical expressions; disagreement permanently loses that fact.
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
    // Facts describe node entry: Some(map) means reachable, with an exact
    // expression for each listed register. An absent register has unknown value;
    // None means no feasible arrival at this node has been discovered.
    let mut facts = FxHashMap::from_iter([(entry, Some(initial))]);

    // Worklist: nodes whose entry facts need propagating to their successors.
    // Start at entry; revisit a successor whenever its merged facts change.
    let mut pending = VecDeque::from([entry]);
    while let Some(node) = pending.pop_front() {
        let replacements = expression_facts(graph, facts[&node].as_ref().unwrap());
        // Build simultaneous register updates, including assignment priority
        // and holding the incoming value when no assignment applies.
        let updates = updates(ctx, graph, symbols, node);
        for edge in &graph[node].transitions {
            // Contraction already resolved the actions into the edge condition.
            // Only substitute entry facts here; applying updates again is wrong.
            let guard = simplify(ctx, &mut simplifier, edge.guard, &replacements);
            facts.entry(edge.target).or_insert(None);
            if guard == ctx.get_false() {
                continue;
            }
            let mut assumptions = FxHashMap::default();
            assume(ctx, guard, true, &mut assumptions);

            // Transfer function: (entry facts, node actions, selected edge) ->
            // exit facts. Substitute entry values into each update, then simplify
            // under the edge condition. Keep only immutable expressions: a port
            // expression would sample a different cycle if propagated further.
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
            // Merge (join): combine this arrival with the target's other arrivals.
            // The first arrival supplies its facts; later arrivals retain only
            // identical register expressions. Disagreement means unknown.
            let target = facts.get_mut(&edge.target).unwrap();
            let joined = match target.as_ref() {
                None => out,
                Some(old) => old
                    .iter()
                    .filter_map(|(&r, &v)| (out.get(&r) == Some(&v)).then_some((r, v)))
                    .collect(),
            };
            // Changed entry facts require another transfer at the target.
            // An empty worklist means the analysis has reached a fixed point.
            if target.as_ref() != Some(&joined) {
                *target = Some(joined);
                pending.push_back(edge.target);
            }
        }
    }
    facts
}
