// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph};
use patronus::expr::{ExprRef, SerializableIrNode};
use std::collections::{BTreeSet, VecDeque};

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
    let mut seen: BTreeSet<NodeId> = BTreeSet::new();
    let mut q = VecDeque::from([protocol.entry]);
    // for (node_id, node) in protocol.nodes() {
    while !q.is_empty() {
        let node_id = q.pop_front().unwrap();
        let node = protocol[node_id].clone();
        seen.insert(node_id);

        let mut label_parts = vec![];

        // collect action text into the node label
        for action in &node.actions {
            label_parts.push(format!(
                "[{}] {}",
                format_expr(protocol, action.guard),
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
        for transition in &node.transitions {
            let edge_label = if transition.consumes_step {
                format!("{} / step", format_expr(protocol, transition.guard))
            } else {
                format_expr(protocol, transition.guard)
            };
            out.push_str(&format!(
                "  {} -> {} [label=\"{}\"];\n",
                node_id,
                transition.target,
                escape_label(&edge_label)
            ));
            if !seen.contains(&transition.target) {
                q.push_back(transition.target);
            }
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
    match &protocol[op_id] {
        Op::Assign(symbol_id, expr_id) => format!(
            "{} := {}",
            symbols.full_name_from_symbol_id(symbol_id),
            format_expr(protocol, *expr_id)
        ),
        Op::AssertEq(lhs, rhs) => format!(
            "assert_eq({}, {})",
            format_expr(protocol, *lhs),
            format_expr(protocol, *rhs)
        ),
        Op::Fork => "fork".to_string(),
        Op::Done => "done".to_string(),
    }
}

fn format_expr(protocol: &ProtoGraph, expr_ref: ExprRef) -> String {
    let expr = &protocol.expr_ctx[expr_ref];
    match protocol.expr_ctx.get_symbol_name(expr_ref) {
        Some(name) if name.starts_with("__dontcare_") => "X".to_string(),
        _ => expr.serialize_to_str(&protocol.expr_ctx),
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
    use crate::ir::edge_contract::contract_edges;
    use crate::ir::lowering::lower_ast_to_ir;
    use insta::Settings;

    use super::*;

    fn snap(name: &str, filename: &str) {
        let mut handler = DiagnosticHandler::default();
        let parsed = parse_file(filename, &mut handler).unwrap();
        let mut content = String::new();
        for (ast, symbols) in parsed.into_iter() {
            let ir: ProtoGraph = lower_ast_to_ir(ast, &symbols);
            content += "== pre-contract ==\n";
            content += &to_dot_string(&ir, &symbols);
            content += "\n";

            // println!("post contract");
            let mut contracted_ir = ir.clone();
            contract_edges(&mut contracted_ir);
            content += "== post-contract ==\n";
            content += &to_dot_string(&contracted_ir, &symbols);
            content += "\n";
        }

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    #[test]
    fn test_add_d1_dot_snapshot() {
        snap("ir_graphviz_add_d1", "tests/adders/adder_d1/add_d1.prot");
    }

    #[test]
    fn test_add_comb_dot_snapshot() {
        snap("ir_graphviz_add_d0", "tests/adders/adder_d0/add_d0.prot");
    }

    #[test]
    fn test_axis_truncated_include_idle_send_data_dot_snapshot() {
        snap(
            "ir_graphviz_axis_truncated_include_idle_send_data",
            "../monitor/tests/wal/advanced/axis_truncated_include_idle.prot",
        );
    }

    #[test]
    fn test_counter_snapshot() {
        snap("ir_graphviz_counter", "tests/counters/counter.prot");
    }

    #[test]
    fn test_bounded_ready_valid_snapshot() {
        snap(
            "ir_graphviz_bounded_ready_valid",
            "tests/bounded_ready_valid/bounded_rv.prot",
        );
    }
}
