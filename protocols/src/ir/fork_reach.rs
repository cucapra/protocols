use patronus::expr::{Context, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::register_simplify::simplify_registers;

/// add registers for forking, then simplify registers, then return all
/// remaining fork points
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

    let implicit_fork = graph.o(Op::Fork);
    for &node in &nodes {
        let mut requested = ctx.get_false();
        let mut done = None;
        let mut actions = Vec::new();
        for action in graph[node].actions.clone() {
            match graph[action.op] {
                Op::Fork => {
                    // There is at most one fork action per node
                    requested = action.guard;
                    let twice = graph.and_guard(ctx, action.guard, current);
                    actions.push(action);
                    let op = graph.o(Op::InternalAssertFalse);
                    actions.push(Action::new(twice, op));
                }
                Op::Done => {
                    done = Some(action.guard);
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
        let done = done.unwrap_or_else(|| {
            if node == exit {
                ctx.get_true()
            } else {
                ctx.get_false()
            }
        });
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
