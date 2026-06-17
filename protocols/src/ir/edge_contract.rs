use std::collections::BTreeSet;

use crate::ir::proto_graph::{Action, Op, ProtoGraph, Transition};
use patronus::expr::ExprRef;

fn and_guard(protocol: &mut ProtoGraph, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
    if lhs == protocol.true_id() {
        rhs
    } else if rhs == protocol.true_id() {
        lhs
    } else if lhs == rhs {
        lhs
    } else {
        protocol.expr_ctx.and(lhs, rhs)
    }
}

fn not_guard(protocol: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    protocol.expr_ctx.not(guard)
}

fn or_guard(protocol: &mut ProtoGraph, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
    if lhs == protocol.true_id() || rhs == protocol.true_id() {
        protocol.true_id()
    } else if lhs == rhs {
        lhs
    } else {
        let not_lhs = not_guard(protocol, lhs);
        let not_rhs = not_guard(protocol, rhs);
        let both_not = and_guard(protocol, not_lhs, not_rhs);
        not_guard(protocol, both_not)
    }
}

fn append_action(
    protocol: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    fork_overlap_guard: &mut Option<ExprRef>,
    action: Action,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, rhs) => {
            let default_value = protocol
                .symbol_expr(symbol_id)
                .unwrap_or_else(|| panic!("missing lowered symbol expression for {symbol_id}"));

            // By invariant, there can be at most one existing assignment for this symbol.
            if let Some(existing_action) = actions.iter_mut().find(|prior_action| {
                matches!(protocol[prior_action.op], Op::Assign(prior_symbol_id, _) if prior_symbol_id == symbol_id)
            }) {
                let existing_rhs = match protocol[existing_action.op].clone() {
                    Op::Assign(_, existing_rhs) => existing_rhs,
                    _ => unreachable!(),
                };
                let merged_rhs = if action.guard == protocol.true_id() {
                    rhs
                } else {
                    protocol.expr_ctx.ite(action.guard, rhs, existing_rhs)
                };
                let new_op = protocol.o(Op::Assign(symbol_id, merged_rhs));
                existing_action.guard = protocol.true_id();
                existing_action.op = new_op;
            } else {
                let merged_rhs = if action.guard == protocol.true_id() {
                    rhs
                } else {
                    protocol.expr_ctx.ite(action.guard, rhs, default_value)
                };
                actions.push(Action::new(
                    protocol.true_id(),
                    protocol.o(Op::Assign(symbol_id, merged_rhs)),
                ));
            }
        }
        Op::Fork => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Fork))
            {
                let overlap = and_guard(protocol, existing_action.guard, action.guard);
                *fork_overlap_guard = Some(match fork_overlap_guard.take() {
                    Some(existing_overlap) => or_guard(protocol, existing_overlap, overlap),
                    None => overlap,
                });
                existing_action.guard = or_guard(protocol, existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::Done => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Done))
            {
                existing_action.guard = or_guard(protocol, existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::AssertEq(_, _) => {
            actions.push(action);
        }
        Op::InternalAssert => unreachable!(),
    }
}

fn assert_no_non_step_cycles(protocol: &ProtoGraph) {
    fn dfs(
        protocol: &ProtoGraph,
        node_id: crate::ir::proto_graph::NodeId,
        visited: &mut BTreeSet<crate::ir::proto_graph::NodeId>,
        active: &mut BTreeSet<crate::ir::proto_graph::NodeId>,
    ) {
        if active.contains(&node_id) {
            panic!("non-step cycle detected at {}", node_id);
        }

        if !visited.insert(node_id) {
            return;
        }

        active.insert(node_id);
        for transition in &protocol[node_id].transitions {
            if !transition.consumes_step {
                dfs(protocol, transition.target, visited, active);
            }
        }
        active.remove(&node_id);
    }

    let mut visited = BTreeSet::new();
    let mut active = BTreeSet::new();

    for (node_id, _) in protocol.nodes() {
        if !visited.contains(&node_id) {
            dfs(protocol, node_id, &mut visited, &mut active);
        }
    }
}

pub fn contract_edges(protocol: &mut ProtoGraph) {
    assert_no_non_step_cycles(protocol);

    let node_ids = protocol
        .nodes()
        .map(|(node_id, _)| node_id)
        .collect::<Vec<_>>();

    for source_node_id in node_ids.into_iter().rev() {
        let mut contracted_actions = Vec::with_capacity(protocol[source_node_id].actions.len());
        let mut fork_overlap_guard = None;
        for action in protocol[source_node_id].actions.clone() {
            append_action(protocol, &mut contracted_actions, &mut fork_overlap_guard, action);
        }

        let (mut step_transitions, mut pending_transitions): (Vec<_>, Vec<_>) = protocol
            [source_node_id]
            .transitions
            .clone()
            .into_iter()
            .partition(|transition| transition.consumes_step);

        while let Some(transition) = pending_transitions.pop() {
            assert!(!transition.consumes_step);

            let target_node_id = transition.target;
            let incoming_guard = transition.guard;
            let target_actions = protocol[target_node_id].actions.clone();
            let target_transitions = protocol[target_node_id].transitions.clone();

            for action in target_actions {
                let merged_action =
                    Action::with_guard(&action, and_guard(protocol, incoming_guard, action.guard));
                append_action(
                    protocol,
                    &mut contracted_actions,
                    &mut fork_overlap_guard,
                    merged_action,
                );
            }

            for target_transition in target_transitions.into_iter().rev() {
                let contracted_transition = Transition::with_guard(
                    &target_transition,
                    and_guard(protocol, incoming_guard, target_transition.guard),
                );
                if contracted_transition.consumes_step {
                    step_transitions.push(contracted_transition);
                } else {
                    pending_transitions.push(contracted_transition);
                }
            }
        }

        let internal_assert_op = fork_overlap_guard.map(|_| protocol.o(Op::InternalAssert));
        let source_node = protocol.node_mut(source_node_id);
        source_node.actions = contracted_actions;
        if let (Some(fork_overlap_guard), Some(internal_assert_op)) =
            (fork_overlap_guard, internal_assert_op)
        {
            source_node
                .actions
                .push(Action::new(fork_overlap_guard, internal_assert_op));
        }
        source_node.transitions = step_transitions;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;

    #[test]
    fn synthesizes_internal_assert_for_overlapping_forks() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into()));
        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);

        let fork1 = protocol.o(Op::Fork);
        let fork2 = protocol.o(Op::Fork);
        protocol.node_mut(protocol.entry).actions = vec![
            Action::new(p, fork1),
            Action::new(q, fork2),
        ];

        contract_edges(&mut protocol);

        let expected_fork_guard = protocol.expr_ctx.or(p, q);
        let expected_overlap = protocol.expr_ctx.and(p, q);
        let actions = &protocol[protocol.entry].actions;
        assert_eq!(actions.len(), 2);
        assert!(matches!(protocol[actions[0].op], Op::Fork));
        assert!(matches!(protocol[actions[1].op], Op::InternalAssert));
        assert_eq!(actions[0].guard, expected_fork_guard);
        assert_eq!(actions[1].guard, expected_overlap);
    }
}
