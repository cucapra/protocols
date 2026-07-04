// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::serialize::serialize_bitvec;
use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use baa::BitVecValue;
use patronus::expr::{Expr, ExprRef};
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

    let mut seen: BTreeSet<NodeId> = BTreeSet::new();
    seen.insert(protocol.entry);
    let mut q = VecDeque::from([protocol.entry]);
    while let Some(node_id) = q.pop_front() {
        let node = protocol[node_id].clone();

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
            // pruning heuristic: skip dead (false-guarded) transitions
            if transition.guard == protocol.false_id() {
                continue;
            }
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
            if seen.insert(transition.target) {
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
        Op::Assign(symbol_id, assignment) => format!(
            "{} := {}",
            symbols.full_name_from_symbol_id(symbol_id),
            format_assignment(protocol, assignment)
        ),
        Op::AssertEq(lhs, rhs) => format!(
            "assert_eq({}, {})",
            format_expr(protocol, *lhs),
            format_expr(protocol, *rhs)
        ),
        Op::Fork => "fork".to_string(),
        Op::InternalAssertFalse => "internal_assert_false".to_string(),
        Op::Done => "done".to_string(),
    }
}

fn format_assignment(protocol: &ProtoGraph, assignment: &Assignment) -> String {
    let mut parts = Vec::new();
    if assignment.dont_care != protocol.false_id() {
        parts.push(format!(
            "X if {}",
            format_expr(protocol, assignment.dont_care)
        ));
    }
    for (guard, rhs) in &assignment.concretes {
        parts.push(format!(
            "{} if {}",
            format_expr(protocol, *rhs),
            format_expr(protocol, *guard)
        ));
    }
    if parts.is_empty() {
        "internal_assert_false".to_string()
    } else {
        parts.join("; ")
    }
}

pub(crate) fn format_expr(protocol: &ProtoGraph, expr_ref: ExprRef) -> String {
    if protocol.dont_cares.contains(&expr_ref) {
        "X".to_string()
    } else {
        format_expr_node(protocol, expr_ref)
    }
}

fn format_expr_node(protocol: &ProtoGraph, expr_ref: ExprRef) -> String {
    match &protocol.expr_ctx[expr_ref] {
        Expr::BVSymbol { name, .. } => protocol.expr_ctx[*name].to_string(),
        Expr::BVLiteral(value) => {
            let value = BitVecValue::from(value.get(&protocol.expr_ctx));
            serialize_bitvec(&value, false)
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            let inner = format_expr(protocol, *e);
            if hi == lo {
                format!("{inner}[{hi}]")
            } else {
                format!("{inner}[{hi}:{lo}]")
            }
        }
        Expr::BVNot(e, _) => format!("not({})", format_expr(protocol, *e)),
        Expr::BVEqual(a, b) => format!(
            "eq({}, {})",
            format_expr(protocol, *a),
            format_expr(protocol, *b)
        ),
        Expr::BVConcat(a, b, _) => {
            format!(
                "concat({}, {})",
                format_expr(protocol, *a),
                format_expr(protocol, *b)
            )
        }
        Expr::BVAnd(a, b, _) => {
            format!(
                "and({}, {})",
                format_expr(protocol, *a),
                format_expr(protocol, *b)
            )
        }
        Expr::BVOr(a, b, _) => {
            format!(
                "or({}, {})",
                format_expr(protocol, *a),
                format_expr(protocol, *b)
            )
        }
        Expr::BVAdd(a, b, _) => format!(
            "add({}, {})",
            format_expr(protocol, *a),
            format_expr(protocol, *b)
        ),
        Expr::BVIte { cond, tru, fals } => {
            format!(
                "ite({}, {}, {})",
                format_expr(protocol, *cond),
                format_expr(protocol, *tru),
                format_expr(protocol, *fals)
            )
        }
        _ => panic!(
            "unsupported expression in graphviz formatter: {:?}",
            protocol.expr_ctx[expr_ref]
        ),
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

    use super::*;
    use crate::frontend;
    use super::*;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::ir::edge_contract::{contract_edges, normalize_assignments};
    use crate::ir::lowering::lower_ast_to_ir;
    use crate::ir::reaching_defs::{
        AssignmentValue, ReachingDefs, exists_conflicts, format_reaching_defs, reaching_definitions,
    };
    use insta::Settings;

    use rustc_hash::FxHashMap;
    use crate::ir::propagate_assigns::propagate_assignments;

    fn snap(name: &str, filename: &str) {
        let mut handler = DiagnosticHandler::default();
        let ast = frontend(&[filename], &mut handler, false).unwrap();
        let mut content = String::new();
        let st = &ast.st;
        for proto_ast in ast.protos {
            let mut ir: ProtoGraph = lower_ast_to_ir(proto_ast, &st);
            content += "== pre-contract ==\n";
            content += &to_dot_string(&ir, st);
            content += "\n";

            // println!("post contract");
            let mut contracted_ir = ir.clone();
            contract_edges(&mut contracted_ir, st);
            content += "== post-contract ==\n";
            content += &to_dot_string(&contracted_ir, st);
            content += "\n";

            // run the reaching definitions analysis
            let reaching_defs = reaching_definitions(&mut ir, &st);

            // pretty print the reaching definitions
            // content += "== reaching-defs ==\n";
            // // content += &format_reaching_defs(&ir, &symbols, &reaching_defs);
            // // content += "\n";
            // content += exists_conflicts(&reaching_defs, &ir).to_string().as_str();
            // content += "\n";

            // print post-propagation of assignments
            propagate_assignments(&mut contracted_ir, &symbols, &reaching_defs);
            content += "== post-propagation ==\n";
            content += &to_dot_string(&ir, &symbols);
            content += "\n";
            

            let mut assignment_normalized_ir = contracted_ir.clone();
            normalize_assignments(&mut assignment_normalized_ir, st);
            content += "== post-normalize ==\n";
            content += &to_dot_string(&assignment_normalized_ir, st);
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
        snap("ir_graphviz_add_d1", "../tests/adders/adder_d1/add_d1.prot");
    }

    #[test]
    fn test_add_comb_dot_snapshot() {
        snap("ir_graphviz_add_d0", "../tests/adders/adder_d0/add_d0.prot");
    }

    #[test]
    fn test_axis_truncated_include_idle_send_data_dot_snapshot() {
        snap(
            "ir_graphviz_axis_truncated_include_idle_send_data",
            "../tests/wal/advanced/axis_truncated_include_idle.prot",
        );
    }

    #[test]
    fn test_counter_snapshot() {
        snap("ir_graphviz_counter", "../tests/counters/counter.prot");
    }

    #[test]
    fn test_bounded_ready_valid_snapshot() {
        snap(
            "ir_graphviz_bounded_ready_valid",
            "../tests/bounded_ready_valid/bounded_rv.prot",
        );
    }
}
