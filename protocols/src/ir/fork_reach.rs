use patronus::expr::{Context, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::register_simplify::simplify_registers;

/// Make fork history explicit, then eliminate it with ordinary register
/// simplification. Completion launches only when no explicit fork has occurred.
pub fn fork_graft_points(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &mut SymbolTable,
    entry: NodeId,
    exit: NodeId,
) -> Vec<(NodeId, ExprRef)> {
    let register = graph.add_register(ctx, symbols, "$has_forked", 1);
    let current = graph.symbol_expr(register).unwrap();
    let nodes = graph.reachable_node_ids(ctx, entry);
    // A distinct operation ID identifies the implicit-fork markers for removal
    // after the ordinary rewriter has simplified their guards.
    let implicit_fork = graph.o(Op::Fork);
    for &node in &nodes {
        let mut requested = ctx.get_false();
        let mut done = if node == exit {
            ctx.get_true()
        } else {
            ctx.get_false()
        };
        let mut actions = Vec::new();
        for action in graph[node].actions.clone() {
            match graph[action.op] {
                Op::Fork => {
                    requested = graph.or_guard(ctx, requested, action.guard);
                    let not_forked = graph.not_guard(ctx, current);
                    let guard = graph.and_guard(ctx, action.guard, not_forked);
                    actions.push(action.with_guard(guard));
                    let twice = graph.and_guard(ctx, action.guard, current);
                    let op = graph.o(Op::InternalAssertFalse);
                    actions.push(Action::new(twice, op));
                }
                Op::Done => {
                    done = graph.or_guard(ctx, done, action.guard);
                    actions.push(action);
                }
                _ => actions.push(action),
            }
        }
        let next = ctx.ite(requested, ctx.get_true(), current);
        let op = graph.o(Op::Assign(
            register,
            Assignment::concrete(ctx.get_false(), ctx.get_true(), next),
        ));
        actions.push(Action::new(ctx.get_true(), op));
        // This expression sees explicit forks from the same node as completion.
        let not_forked = ctx.not(next);
        let implicit = ctx.and(done, not_forked);
        actions.push(Action::new(implicit, implicit_fork));
        graph.node_mut(node).actions = actions;
    }
    let initial = FxHashMap::from_iter([(register, ctx.get_false())]);
    let dead = simplify_registers(ctx, graph, symbols, entry, &initial, &FxHashSet::default());
    assert!(
        dead.contains(&register),
        "fork history requires unsupported register state at {entry}"
    );
    let mut grafts = Vec::new();
    for node in graph.reachable_node_ids(ctx, entry) {
        for action in &graph[node].actions {
            if matches!(graph[action.op], Op::Fork) {
                grafts.push((node, action.guard));
            }
        }
    }
    // Remove markers even in nodes made unreachable by simplification. Explicit
    // fork actions remain part of the graph, as before.
    for node in nodes {
        graph
            .node_mut(node)
            .actions
            .retain(|a| a.op != implicit_fork);
    }
    graph.garbage_collect_ops();
    grafts
}
