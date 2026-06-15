use crate::frontend::ast::{BinOp, Expr};
use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Action, ProtoGraph, Transition};

/// Finds the rightmost eligible edge and contracts it.
/// Returns `true` if there was an edge to contract.
fn contract_edge(protocol: &mut ProtoGraph, _symbols: &SymbolTable) -> bool {
    let mut nodes: Vec<_> = protocol.nodes().map(|(node_id, _)| node_id).collect();
    nodes.reverse();

    for lhs_id in nodes {
        let transitions = protocol[lhs_id].transition_iter().cloned().collect::<Vec<_>>();
        for (transition_idx, transition) in transitions.into_iter().enumerate().rev() {
            if transition.consumes_step {
                continue;
            }

            let rhs_id = transition.target;
            let rhs_actions = protocol[rhs_id].action_iter().cloned().collect::<Vec<_>>();
            let rhs_transitions = protocol[rhs_id].transition_iter().cloned().collect::<Vec<_>>();
            let lhs_guard = transition.guard;

            let mut merged_actions = Vec::with_capacity(rhs_actions.len());
            for action in rhs_actions {
                let guard = protocol.e(Expr::Binary(BinOp::Add, lhs_guard, action.guard));
                merged_actions.push(Action::new(guard, action.op));
            }

            let mut merged_transitions = Vec::with_capacity(rhs_transitions.len());
            for rhs_transition in rhs_transitions {
                let guard = protocol.e(Expr::Binary(BinOp::Add, lhs_guard, rhs_transition.guard));
                merged_transitions.push(Transition::new(
                    guard,
                    rhs_transition.target,
                    rhs_transition.consumes_step,
                ));
            }

            let lhs_node = protocol.node_mut(lhs_id);
            lhs_node.transitions_mut().remove(transition_idx);
            lhs_node.actions_mut().extend(merged_actions);
            lhs_node.transitions_mut().extend(merged_transitions);

            return true;
        }
    }

    false
}

/// Run `contract_edge` until there are no more edges to contract.
pub fn contract_edges(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    while contract_edge(protocol, symbols) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::parser::parse_file;
    use crate::ir::lowering::lower_ast_to_ir;
    use tempfile::NamedTempFile;

    fn lower_with_symbols(source: &str) -> (ProtoGraph, SymbolTable) {
        let file = NamedTempFile::new().unwrap();
        std::fs::write(file.path(), source).unwrap();

        let mut handler = DiagnosticHandler::default();
        let parsed = parse_file(file.path(), &mut handler).unwrap();
        assert_eq!(parsed.len(), 1);
        let (ast, symbols) = parsed.into_iter().next().unwrap();
        (lower_ast_to_ir(ast), symbols)
    }

    #[test]
    fn contracts_non_step_edges_and_leaves_step_edges_in_place() {
        let (mut protocol, symbols) = lower_with_symbols(
            r#"
            struct Dummy {
              in a: u32,
              out b: u32,
            }

            prot pipe<dut: Dummy>(a: u32, b: u32) {
              dut.a := a;
              step();
              assert_eq(b, dut.b);
            }
            "#,
        );

        contract_edges(&mut protocol, &symbols);

        let entry = &protocol[protocol.entry];
        assert!(entry.action_iter().count() >= 1);
        assert_eq!(entry.transition_iter().count(), 1);
        assert!(entry.transition_iter().next().unwrap().consumes_step);
    }
}
