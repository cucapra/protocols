// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::serialize::serialize_bitvec;
use crate::frontend::symbol::SymbolTable;
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use baa::BitVecValue;
use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode};

/// generate a DOT file for graphviz from the IR
pub fn to_dot_string(ctx: &Context, protocol: &ProtoGraph, symbols: &SymbolTable) -> String {
    to_dot_string_with_node_labels(ctx, protocol, symbols, &[])
}

pub fn to_dot_string_from_entry(
    ctx: &Context,
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    entry: NodeId,
) -> String {
    to_dot_string_with_node_labels_from_entry(ctx, protocol, symbols, &[], entry)
}

/// Add descriptive labels to distinguished states, such as a monitor's bad state.
pub fn to_dot_string_with_node_labels(
    ctx: &Context,
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    labels: &[(NodeId, &str)],
) -> String {
    to_dot_string_with_node_labels_from_entry(ctx, protocol, symbols, labels, protocol.entry)
}

fn to_dot_string_with_node_labels_from_entry(
    ctx: &Context,
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    labels: &[(NodeId, &str)],
    entry: NodeId,
) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "digraph \"{}\" {{\n",
        escape_label(&protocol.name)
    ));
    out.push_str("  rankdir=LR;\n");
    out.push_str("  node [shape=box];\n");
    out.push_str("  entry_marker [shape=plain,label=\"ENTRY\"];\n");
    out.push_str(&format!("  entry_marker -> {};\n", entry));

    for node_id in protocol.reachable_node_ids(ctx, entry) {
        let node = protocol[node_id].clone();

        let mut label_parts = vec![];
        if let Some((_, label)) = labels.iter().find(|(id, _)| *id == node_id) {
            label_parts.push((*label).to_string());
        }

        // collect action text into the node label
        for action in &node.actions {
            label_parts.push(format!(
                "[{}] {}",
                format_expr(ctx, protocol, action.guard),
                format_op(ctx, protocol, symbols, action.op)
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
            if transition.guard == ctx.get_false() {
                continue;
            }
            let mut edge_label = if transition.consumes_step {
                format!("{} / step", format_expr(ctx, protocol, transition.guard))
            } else {
                format_expr(ctx, protocol, transition.guard)
            };
            if !transition.rotations.is_empty() {
                let rotations = transition
                    .rotations
                    .iter()
                    .map(|rotation| {
                        if rotation.amount == 1 {
                            format!("R_{}", rotation.protocol)
                        } else {
                            format!("R_{}^{}", rotation.protocol, rotation.amount)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                edge_label.push_str(&format!(" / {rotations}"));
            }
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
    ctx: &Context,
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    op_id: crate::ir::proto_graph::OpId,
) -> String {
    match &protocol[op_id] {
        Op::Assign(symbol_id, assignment) => format!(
            "{} := {}",
            symbols.full_name_from_symbol_id(symbol_id),
            format_assignment(ctx, protocol, assignment)
        ),
        Op::AssertEq(lhs, rhs) => format!(
            "assert_eq({}, {})",
            format_expr(ctx, protocol, *lhs),
            format_expr(ctx, protocol, *rhs)
        ),
        Op::Fork => "fork".to_string(),
        Op::InternalAssertFalse => "internal_assert_false".to_string(),
        Op::Done => "done".to_string(),
    }
}

/// Text view of the prepared DUT assignments, used by the legacy CLI flag.
pub fn format_assignments(ctx: &Context, graph: &ProtoGraph, symbols: &SymbolTable) -> String {
    let mut out = String::new();
    for (id, node) in graph.nodes() {
        out.push_str(&format!("{id}:\n"));
        let mut assignments = node
            .actions
            .iter()
            .filter_map(|a| match &graph[a.op] {
                Op::Assign(pin, assignment) if symbols[*pin].is_in_port() => {
                    Some((symbols[*pin].full_name(symbols), assignment))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assignments.sort_by(|a, b| a.0.cmp(&b.0));
        for (name, assignment) in assignments {
            out.push_str(&format!(
                "  {name}: {}\n",
                format_assignment(ctx, graph, assignment)
            ));
        }
    }
    out
}

fn format_assignment(ctx: &Context, protocol: &ProtoGraph, assignment: &Assignment) -> String {
    let mut parts = Vec::new();
    if assignment.dont_care != ctx.get_false() {
        parts.push(format!(
            "X{}",
            format_guard(ctx, protocol, assignment.dont_care)
        ));
    }
    for (guard, rhs) in &assignment.concretes {
        parts.push(format!(
            "{}{}",
            format_expr(ctx, protocol, *rhs),
            format_guard(ctx, protocol, *guard)
        ));
    }
    if parts.is_empty() {
        "internal_assert_false".to_string()
    } else {
        parts.join("; ")
    }
}

fn format_guard(ctx: &Context, protocol: &ProtoGraph, guard: ExprRef) -> String {
    if guard == ctx.get_true() {
        "".to_string()
    } else {
        format!(" if {}", format_expr(ctx, protocol, guard))
    }
}

pub fn format_expr(ctx: &Context, protocol: &ProtoGraph, expr_ref: ExprRef) -> String {
    if protocol.dont_cares.contains(&expr_ref) {
        "X".to_string()
    } else {
        format_expr_node(ctx, protocol, expr_ref)
    }
}

fn format_expr_node(ctx: &Context, protocol: &ProtoGraph, expr_ref: ExprRef) -> String {
    match &ctx[expr_ref] {
        Expr::BVSymbol { name, .. } => ctx[*name].to_string(),
        Expr::BVLiteral(value) => {
            let value = BitVecValue::from(value.get(ctx));
            serialize_bitvec(&value, false)
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            let inner = format_expr(ctx, protocol, *e);
            if hi == lo {
                format!("{inner}[{hi}]")
            } else {
                format!("{inner}[{hi}:{lo}]")
            }
        }
        Expr::BVNot(e, _) => format!("not({})", format_expr(ctx, protocol, *e)),
        Expr::BVZeroExt { e, by, .. } => {
            format!("zero_extend({}, {by})", format_expr(ctx, protocol, *e))
        }
        Expr::BVShiftLeft(a, b, _) => format!(
            "shl({}, {})",
            format_expr(ctx, protocol, *a),
            format_expr(ctx, protocol, *b)
        ),
        Expr::BVEqual(a, b) => format!(
            "eq({}, {})",
            format_expr(ctx, protocol, *a),
            format_expr(ctx, protocol, *b)
        ),
        Expr::BVConcat(a, b, _) => {
            format!(
                "concat({}, {})",
                format_expr(ctx, protocol, *a),
                format_expr(ctx, protocol, *b)
            )
        }
        Expr::BVAnd(a, b, _) => {
            format!(
                "and({}, {})",
                format_expr(ctx, protocol, *a),
                format_expr(ctx, protocol, *b)
            )
        }
        Expr::BVOr(a, b, _) => {
            format!(
                "or({}, {})",
                format_expr(ctx, protocol, *a),
                format_expr(ctx, protocol, *b)
            )
        }
        Expr::BVAdd(a, b, _) => format!(
            "add({}, {})",
            format_expr(ctx, protocol, *a),
            format_expr(ctx, protocol, *b)
        ),
        Expr::BVIte { cond, tru, fals } => {
            format!(
                "ite({}, {}, {})",
                format_expr(ctx, protocol, *cond),
                format_expr(ctx, protocol, *tru),
                format_expr(ctx, protocol, *fals)
            )
        }
        Expr::BVGreaterEqual(a, b) => format!(
            "ge({}, {})",
            format_expr(ctx, protocol, *a),
            format_expr(ctx, protocol, *b)
        ),
        _ => ctx[expr_ref].serialize_to_str(ctx),
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
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::driver_to_monitor::{
        MonitorAutomaton, convert_driver_to_capturing_driver, convert_driver_to_monitor,
        simplify_monitor
    };
    use crate::ir::edge_contract::{contract_edges, normalize_assignments};
    use crate::ir::joint_driver::build_joint_driver_automaton;
    use crate::ir::joint_monitor::build_joint_monitor_automaton;
    use crate::ir::lowering::lower_ast_to_ir;
    use crate::ir::propagate_assigns::{insert_assignment_registers, simplify_assignments};
    use insta::Settings;

    fn snap(name: &str, filename: &str) -> (Context, SymbolTable, Vec<MonitorAutomaton>) {
        let mut handler = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let mut content = String::new();
        let mut monitors = Vec::new();
        let module = require_single_module(modules, &[filename]).unwrap();
        let mut ctx = Context::default();
        for proto_ast in module.protos {
            let ir: ProtoGraph = lower_ast_to_ir(&mut ctx, proto_ast, &mut symbols);
            content += "== pre-contract ==\n";
            content += &to_dot_string(&ctx, &ir, &symbols);
            content += "\n";

            let mut contracted_ir = ir.clone();
            contract_edges(&mut ctx, &mut contracted_ir, &symbols);

            content += "== post-contract ==\n";
            content += &to_dot_string(&ctx, &contracted_ir, &symbols);
            content += "\n";

            let entry = contracted_ir.entry;
            let initial =
                insert_assignment_registers(&mut ctx, &mut contracted_ir, &mut symbols, entry);

            simplify_assignments(&mut ctx, &mut contracted_ir, &symbols, &initial);
            content += "== post-simplification ==\n";
            content += &to_dot_string(&ctx, &contracted_ir, &symbols);
            content += "\n";

            let mut assignment_normalized_ir = contracted_ir.clone();
            normalize_assignments(&mut ctx, &mut assignment_normalized_ir, &symbols);
            content += "== post-normalize ==\n";
            content += &to_dot_string(&ctx, &assignment_normalized_ir, &symbols);
            content += "\n";

            assignment_normalized_ir.garbage_collect_unreachable(&ctx);
            let monitor =
                convert_driver_to_monitor(&mut ctx, assignment_normalized_ir, &mut symbols)
                    .unwrap();
            let monitor = simplify_monitor(&mut ctx, monitor, &mut symbols);
            content += "== simplified monitor ==\n";
            content += &monitor.to_dot_string(&ctx, &symbols);
            content += "\n";
            monitors.push(monitor);
        }

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
        (ctx, symbols, monitors)
    }
    #[test]
    fn test_capturing_driver_snapshot() {
        let filename = "../tests/adders/adder_d1/add_d1.prot";
        let mut handler = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let ast = module.protos.into_iter().next().unwrap();
        let mut ctx = Context::default();
        let mut graph = lower_ast_to_ir(&mut ctx, ast, &mut symbols);
        let entry = graph.entry;
        contract_edges(&mut ctx, &mut graph, &symbols);
        let initial = insert_assignment_registers(&mut ctx, &mut graph, &mut symbols, entry);

        simplify_assignments(&mut ctx, &mut graph, &symbols, &initial);
        normalize_assignments(&mut ctx, &mut graph, &symbols);
        graph.garbage_collect_unreachable(&ctx);
        let driver = convert_driver_to_capturing_driver(&mut ctx, graph, &mut symbols).unwrap();
        let driver = simplify_monitor(&mut ctx, driver, &mut symbols);
        let dot = driver.to_dot_string(&ctx, &symbols);
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| insta::assert_snapshot!("ir_graphviz_capturing_driver", dot));
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

    #[test]
    fn test_overlapping_parameter_slices_snapshot() {
        let (mut ctx, symbols, monitors) = snap(
            "ir_graphviz_overlapping_parameter_slices",
            "../tests/monitors/overlapping_slices.prot",
        );
        let graph = &monitors[0].graph;
        let pin = |name: &str| {
            let pin = graph
                .dut_pins(&symbols)
                .find(|&pin| symbols[pin].name() == name)
                .unwrap();
            graph.symbol_expr(pin).unwrap()
        };
        let a = ctx.slice(pin("a"), 2, 1);
        let b = ctx.slice(pin("b"), 1, 0);
        let checks = graph
            .nodes()
            .flat_map(|(_, node)| &node.actions)
            .filter_map(|action| match graph[action.op] {
                Op::AssertEq(lhs, rhs) => Some((action.guard, lhs, rhs)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(checks.len(), 1, "the overlap requires exactly one check");
        let (guard, lhs, rhs) = checks[0];
        assert_eq!(guard, ctx.get_true());
        assert!(
            (lhs == a && rhs == b) || (lhs == b && rhs == a),
            "expected assert_eq(DUT.a[2:1], DUT.b[1:0])"
        );
    }

    fn joint_snap(name: &str, filename: &str, selected: &[&str]) {
        let mut handler = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let protocols = module
            .protos
            .iter()
            .filter(|protocol| selected.contains(&protocol.name.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        let mut ctx = Context::default();
        let driver =
            build_joint_driver_automaton(&mut ctx, &module, protocols.clone(), &mut symbols)
                .unwrap();
        let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
        let driver_dot = to_dot_string(&ctx, &driver.graph, &symbols);
        let monitor_dot = monitor.to_dot_string(&ctx, &symbols);
        if let Some(directory) = std::env::var_os("PROTOCOLS_JOINT_MONITOR_DOT_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(directory.join(format!("{name}_driver.dot")), &driver_dot).unwrap();
            std::fs::write(directory.join(format!("{name}_monitor.dot")), &monitor_dot).unwrap();
        }
        let content =
            format!("== unbounded-driver ==\n{driver_dot}\n== unbounded-monitor ==\n{monitor_dot}");
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| insta::assert_snapshot!(name, content));
    }

    #[test]
    fn test_joint_alu_snapshot() {
        joint_snap(
            "ir_graphviz_joint_alu",
            "../tests/alus/alu_d1.prot",
            &["add", "sub", "and", "or"],
        );
    }

    #[test]
    fn test_joint_axis_send_data_snapshot() {
        joint_snap(
            "ir_graphviz_joint_axis_send_data",
            "../tests/wal/advanced/axis.prot",
            &["send_data"],
        );
    }
}
