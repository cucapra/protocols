use std::collections::{BTreeSet, VecDeque};

use crate::ir::proto_graph::{Action, Op, ProtoGraph, Transition};
use patronus::expr::ExprRef;

fn append_action(
    protocol: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    internal_assert_guard: &mut Option<ExprRef>,
    action: Action,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, rhs) => {
            let default_value = protocol.symbol_expr(symbol_id).unwrap_or_else(|| {
                unreachable!("missing lowered symbol expression for {symbol_id}")
            });

            // By invariant, there can be at most one existing assignment for this symbol.
            if let Some(existing_action) = actions.iter_mut().find(|prior_action| {
                matches!(protocol[prior_action.op], Op::Assign(prior_symbol_id, _) if prior_symbol_id == symbol_id)
            }) {
                let existing_rhs = match protocol[existing_action.op].clone() {
                    Op::Assign(_, existing_rhs) => existing_rhs,
                    _ => unreachable!(),
                };
                let existing_rhs = if existing_action.guard == protocol.true_id() {
                    existing_rhs
                } else {
                    protocol
                        .expr_ctx
                        .ite(existing_action.guard, existing_rhs, default_value)
                };
                let merged_rhs = protocol.expr_ctx.ite(action.guard, rhs, existing_rhs);
                let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
                let merged_rhs = simplifier.simplify(expr_ctx, merged_rhs);
                let new_op = protocol.o(Op::Assign(symbol_id, merged_rhs));
                existing_action.guard = protocol.true_id();
                existing_action.op = new_op;
            } else {
                actions.push(action);
            }
        }
        Op::Fork => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Fork))
            {
                let overlap = protocol.and_guard(existing_action.guard, action.guard);
                *internal_assert_guard = Some(match internal_assert_guard.take() {
                    Some(existing_overlap) => protocol.or_guard(existing_overlap, overlap),
                    None => overlap,
                });
                existing_action.guard = protocol.or_guard(existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::Done => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Done))
            {
                existing_action.guard = protocol.or_guard(existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::AssertEq(_, _) => {
            actions.push(action);
        }
        Op::InternalAssertFalse => {
            actions.push(action);
        }
    }
}

pub fn contract_edges(protocol: &mut ProtoGraph) {
    let node_ids = protocol
        .nodes()
        .map(|(node_id, _)| node_id)
        .collect::<Vec<_>>();

    for source_node_id in node_ids.into_iter().rev() {
        let mut contracted_actions = Vec::with_capacity(protocol[source_node_id].actions.len());
        let mut internal_assert_guard = None;
        for action in protocol[source_node_id].actions.clone() {
            append_action(
                protocol,
                &mut contracted_actions,
                &mut internal_assert_guard,
                action,
            );
        }

        let (mut step_transitions, pending_transitions): (Vec<_>, Vec<_>) = protocol
            [source_node_id]
            .transitions
            .clone()
            .into_iter()
            .partition(|transition| transition.consumes_step);

        let mut pending_transitions: VecDeque<_> = pending_transitions
            .into_iter()
            .rev()
            .map(|transition| {
                (transition, {
                    let mut path = BTreeSet::new();
                    path.insert(source_node_id);
                    path
                })
            })
            .collect();

        while let Some((transition, path)) = pending_transitions.pop_front() {
            assert!(!transition.consumes_step);

            let target_node_id = transition.target;
            if path.contains(&target_node_id) {
                internal_assert_guard = Some(match internal_assert_guard.take() {
                    Some(existing_guard) => protocol.or_guard(existing_guard, transition.guard),
                    None => transition.guard,
                });
                continue;
            }

            let incoming_guard = transition.guard;
            let target_actions = protocol[target_node_id].actions.clone();
            let target_transitions = protocol[target_node_id].transitions.clone();
            let mut next_path = path.clone();
            next_path.insert(target_node_id);

            for action in target_actions {
                let merged_action =
                    Action::with_guard(&action, protocol.and_guard(incoming_guard, action.guard));
                append_action(
                    protocol,
                    &mut contracted_actions,
                    &mut internal_assert_guard,
                    merged_action,
                );
            }

            for target_transition in target_transitions.into_iter().rev() {
                let contracted_transition = Transition::with_guard(
                    &target_transition,
                    protocol.and_guard(incoming_guard, target_transition.guard),
                );
                if contracted_transition.consumes_step {
                    step_transitions.push(contracted_transition);
                } else {
                    pending_transitions.push_back((contracted_transition, next_path.clone()));
                }
            }
        }

        if let Some(internal_assert_guard) = internal_assert_guard {
            let internal_assert_op = protocol.o(Op::InternalAssertFalse);
            let source_node = protocol.node_mut(source_node_id);
            source_node.actions = contracted_actions;
            source_node
                .actions
                .push(Action::new(internal_assert_guard, internal_assert_op));
        } else {
            let source_node = protocol.node_mut(source_node_id);
            source_node.actions = contracted_actions;
        }
        protocol.node_mut(source_node_id).transitions = step_transitions;
    }

    // TODO: check all simplifications here
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use patronus::expr::SerializableIrNode;

    #[test]
    fn synthesizes_internal_assert_for_overlapping_forks() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into()));
        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);

        let fork1 = protocol.o(Op::Fork);
        let fork2 = protocol.o(Op::Fork);
        let fork3 = protocol.o(Op::Fork);
        protocol.node_mut(protocol.entry).actions = vec![
            Action::new(p, fork1),
            Action::new(q, fork2),
            Action::new(r, fork3),
        ];

        contract_edges(&mut protocol);

        let actions = &protocol[protocol.entry].actions;
        assert_eq!(actions.len(), 2);
        assert!(matches!(protocol[actions[0].op], Op::Fork));
        assert!(matches!(protocol[actions[1].op], Op::InternalAssertFalse));

        let fork_guard = protocol.expr_ctx[actions[0].guard].serialize_to_str(&protocol.expr_ctx);
        let internal_guard =
            protocol.expr_ctx[actions[1].guard].serialize_to_str(&protocol.expr_ctx);

        // any of the forks can trigger: (p \/ q \/ r)
        assert_eq!(fork_guard, "or(or(p, q), r)");

        // any two of the forks should not trigger at once
        // below expression is equivalent to (p \/ q) /\ (p \/ r) /\ (q \/ r)
        assert_eq!(internal_guard, "or(and(p, q), and(or(p, q), r))");
    }
}
