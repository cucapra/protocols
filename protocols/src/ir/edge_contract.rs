use std::collections::BTreeSet;

use crate::frontend::symbol::SymbolTable;
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
        protocol.exprCtx.and(lhs, rhs)
    }
}

fn not_guard(protocol: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    protocol.exprCtx.not(guard)
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
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    action: Action,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, rhs) => {
            let default_value = protocol.symbol_expr(symbol_id, symbols);

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
                    protocol.exprCtx.ite(action.guard, rhs, existing_rhs)
                };
                let new_op = protocol.o(Op::Assign(symbol_id, merged_rhs));
                existing_action.guard = protocol.true_id();
                existing_action.op = new_op;
            } else {
                let merged_rhs = if action.guard == protocol.true_id() {
                    rhs
                } else {
                    protocol.exprCtx.ite(action.guard, rhs, default_value)
                };
                actions.push(Action::new(
                    protocol.true_id(),
                    protocol.o(Op::Assign(symbol_id, merged_rhs)),
                ));
            }
        }
        Op::Fork | Op::Done => {
            if let Some(existing_action) = actions.iter_mut().find(|prior_action| {
                matches!(
                    (&protocol[prior_action.op], &protocol[action.op]),
                    (Op::Fork, Op::Fork) | (Op::Done, Op::Done)
                )
            }) {
                existing_action.guard = or_guard(protocol, existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::AssertEq(_, _) => {
            actions.push(action);
        }
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

pub fn contract_edges(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    assert_no_non_step_cycles(protocol);

    let node_ids = protocol
        .nodes()
        .map(|(node_id, _)| node_id)
        .collect::<Vec<_>>();

    for source_node_id in node_ids.into_iter().rev() {
        let mut contracted_actions = Vec::with_capacity(protocol[source_node_id].actions.len());
        for action in protocol[source_node_id].actions.clone() {
            append_action(protocol, symbols, &mut contracted_actions, action);
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
                let merged_action = Action::with_guard(
                    &action,
                    and_guard(protocol, incoming_guard, action.guard),
                );
                append_action(protocol, symbols, &mut contracted_actions, merged_action);
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

        let source_node = protocol.node_mut(source_node_id);
        source_node.actions = contracted_actions;
        source_node.transitions = step_transitions;
    }
}
