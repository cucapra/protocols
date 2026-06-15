use crate::frontend::ast::{BinOp, Expr, ExprId};
use crate::ir::proto_graph::{Action, ProtoGraph, Transition};

/// If either side of the guard conjunction is `true`, elide it.
fn and_guard(protocol: &mut ProtoGraph, lhs: ExprId, rhs: ExprId) -> ExprId {
    if lhs == protocol.true_id() {
        rhs
    } else if rhs == protocol.true_id() {
        lhs
    } else {
        protocol.e(Expr::Binary(BinOp::And, lhs, rhs))
    }
}

/// Contract non-step edges from right to left until no more eligible edges remain.
pub fn contract_edges(protocol: &mut ProtoGraph) {
    let node_ids = protocol
        .nodes()
        .map(|(node_id, _)| node_id)
        .collect::<Vec<_>>();

    // iterate nodes
    for lhs_id in node_ids.into_iter().rev() {
        let mut transition_idx = protocol[lhs_id].transitions.len();

        // iterate transitions backwards. for some reason I feel this will prevent
        // duplicate edges; revisit when we have evidence of things going wrong
        // TODO: the backwards iteration logic here is a bit messy
        while transition_idx > 0 {
            transition_idx -= 1;
            let transition = protocol[lhs_id][transition_idx].clone();

            if transition.consumes_step {
                continue;
            }

            let rhs_id = transition.target;
            let lhs_guard = transition.guard;
            let rhs_actions = protocol[rhs_id].actions.clone();
            let rhs_transitions = protocol[rhs_id].transitions.clone();

            // create actions with the transition to RHS guard & the action in RHS guards
            let merged_actions = rhs_actions
                .into_iter()
                .map(|action| Action::new(and_guard(protocol, lhs_guard, action.guard), action.op))
                .collect::<Vec<_>>();
            // create transitions with the transition to RHS guard & the transition from RHS guards
            let merged_transitions = rhs_transitions
                .into_iter()
                .map(|rhs_transition| {
                    Transition::new(
                        and_guard(protocol, lhs_guard, rhs_transition.guard),
                        rhs_transition.target,
                        rhs_transition.consumes_step,
                    )
                })
                .collect::<Vec<_>>();

            // modify the LHS nodes with these
            let lhs_node = protocol.node_mut(lhs_id);
            lhs_node.transitions.remove(transition_idx);
            lhs_node.actions.extend(merged_actions);
            lhs_node.transitions.extend(merged_transitions);

            // Re-scan this node from the right so newly appended transitions
            // introduced by the contraction can themselves be contracted.
            transition_idx = protocol[lhs_id].transitions.len();
        }
    }
}
