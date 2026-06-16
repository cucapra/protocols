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

    for source_node_id in node_ids.into_iter().rev() {
        let mut contracted_actions = protocol[source_node_id].actions.clone();
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

            // Merge actions from the target node into the source node with the
            // source transition guard AND-ed on.
            for action in target_actions {
                contracted_actions.push(Action::with_guard(
                    &action,
                    and_guard(protocol, incoming_guard, action.guard),
                ));
            }

            // Merge transitions out of the target node into the source node with the
            // source transition guard AND-ed on.
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
