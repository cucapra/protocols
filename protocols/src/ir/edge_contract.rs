use std::collections::{BTreeSet, VecDeque};

use crate::ir::proto_graph::{Action, Op, ProtoGraph, Transition};
use patronus::expr::ExprRef;

fn and_guard(protocol: &mut ProtoGraph, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
    if lhs == protocol.true_id() || lhs == rhs {
        rhs
    } else if rhs == protocol.true_id() {
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
    internal_assert_guard: &mut Option<ExprRef>,
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
                *internal_assert_guard = Some(match internal_assert_guard.take() {
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
        Op::InternalAssertFalse => unreachable!(),
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
                    Some(existing_guard) => or_guard(protocol, existing_guard, transition.guard),
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
                    Action::with_guard(&action, and_guard(protocol, incoming_guard, action.guard));
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
                    and_guard(protocol, incoming_guard, target_transition.guard),
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use baa::{BitVecOps, BitVecValue};
    use patronus::expr::{SymbolValueStore, eval_expr};
    use std::convert::TryInto;

    #[test]
    fn synthesizes_internal_assert_for_overlapping_forks() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into()));
        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);

        let fork1 = protocol.o(Op::Fork);
        let fork2 = protocol.o(Op::Fork);
        protocol.node_mut(protocol.entry).actions =
            vec![Action::new(p, fork1), Action::new(q, fork2)];

        contract_edges(&mut protocol);

        let actions = &protocol[protocol.entry].actions;
        assert_eq!(actions.len(), 2);
        assert!(matches!(protocol[actions[0].op], Op::Fork));
        assert!(matches!(protocol[actions[1].op], Op::InternalAssertFalse));

        for (p_val, q_val, expected_fork, expected_overlap) in [
            (false, false, false, false),
            (false, true, true, false),
            (true, false, true, false),
            (true, true, true, true),
        ] {
            let mut store = SymbolValueStore::default();
            store.define_bv(p, &BitVecValue::from_u64(p_val as u64, 1));
            store.define_bv(q, &BitVecValue::from_u64(q_val as u64, 1));

            let fork_guard: BitVecValue = eval_expr(&protocol.expr_ctx, &store, actions[0].guard)
                .try_into()
                .unwrap();
            let internal_guard: BitVecValue =
                eval_expr(&protocol.expr_ctx, &store, actions[1].guard)
                    .try_into()
                    .unwrap();
            assert_eq!(!fork_guard.is_zero(), expected_fork);
            assert_eq!(!internal_guard.is_zero(), expected_overlap);
        }
    }
}
