use crate::frontend::serialize::serialize_expr;
use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Op, ProtoGraph};

/// generate a DOT file for graphviz from the IR
pub fn to_dot_string(protocol: &ProtoGraph, symbols: &SymbolTable) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "digraph \"{}\" {{\n",
        escape_label(&protocol.name)
    ));
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box];\n");
    out.push_str("  entry_marker [shape=plain,label=\"ENTRY\"];\n");
    out.push_str(&format!("  entry_marker -> {};\n", protocol.entry));

    // emit one graphviz node per ir node
    for (node_id, node) in protocol.nodes() {
        let mut label_parts = vec![];

        // collect action text into the node label
        for action in node.action_iter() {
            label_parts.push(format!(
                "[{}] {}",
                serialize_expr(protocol, symbols, &action.guard),
                format_op(protocol, symbols, action.op)
            ));
        }

        // generate a label from the actions (empty label if no actions)
        out.push_str(&format!(
            "  {} [label=\"{}\"];\n",
            node_id,
            escape_label(&label_parts.join("\\n"))
        ));

        // emit graph edges
        for transition in node.transition_iter() {
            let edge_label = if transition.consumes_step {
                format!(
                    "{} / step",
                    serialize_expr(protocol, symbols, &transition.guard)
                )
            } else {
                serialize_expr(protocol, symbols, &transition.guard)
            };
            out.push_str(&format!(
                "  {} -> {} [label=\"{}\"];\n",
                node_id,
                transition.target,
                escape_label(&edge_label)
            ));
        }
    }

    out.push_str("}\n");
    out
}

/// simple serialization for ops. expressions are serialized using existing `serializer.rs` in the frontend
fn format_op(
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    op_id: crate::ir::proto_graph::OpId,
) -> String {
    match protocol.op(op_id) {
        Op::Assign(symbol_id, expr_id) => format!(
            "{} := {}",
            symbols.full_name_from_symbol_id(symbol_id),
            serialize_expr(protocol, symbols, expr_id)
        ),
        Op::AssertEq(lhs, rhs) => format!(
            "assert_eq({}, {})",
            serialize_expr(protocol, symbols, lhs),
            serialize_expr(protocol, symbols, rhs)
        ),
        Op::Fork => "fork".to_string(),
        Op::Done => "done".to_string(),
    }
}

/// makes sure our digraph name is parseable by DOT
fn escape_label(label: &str) -> String {
    // preserve graphviz escapes like \n in labels, only escape quotes here
    label.replace('"', "\\\"")
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::parser::parse_file;
    use crate::ir::lowering::lower_ast_to_ir;
    use insta::Settings;

    use super::*;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    #[test]
    fn test_add_d1_dot_snapshot() {
        let mut handler = DiagnosticHandler::default();
        let parsed = parse_file("tests/adders/adder_d1/add_d1.prot", &mut handler).unwrap();
        let (ast, symbols) = parsed
            .into_iter()
            .find(|(ast, _)| ast.name == "add")
            .unwrap();
        let ir = lower_ast_to_ir(ast);

        let dot = to_dot_string(&ir, &symbols);
        snap("ir_graphviz_add_d1", dot);
    }
}
