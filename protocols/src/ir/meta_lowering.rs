use std::collections::VecDeque;

use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::{contract_edges, contract_edges_from};
use crate::ir::lowering::{Lowerer, lower_ast_to_ir};
use crate::ir::meta_automaton::{
    MetaAutomaton, MetaFrontier, ProtocolTiming, bounded_driver_meta, steady_driver_meta,
};
use crate::ir::meta_graphviz::to_dot;
use crate::ir::meta_timing::analyze_protocol_timing;
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation,
};

struct ProtocolShape {
    /// Pre-cycle zero is the cycle represented by E.
    pre: Vec<NodeId>,
    /// Ordered from the fork cycle through the final post cycle.
    post: Vec<NodeId>,
}

fn reachable_markers(graph: &ProtoGraph, entry: NodeId, fork: bool) -> Vec<NodeId> {
    let mut found = Vec::new();
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::from([entry]);
    while let Some(node_id) = queue.pop_front() {
        if !seen.insert(node_id) {
            continue;
        }
        for action in &graph[node_id].actions {
            let matches = if fork {
                matches!(graph[action.op], Op::Fork)
            } else {
                matches!(graph[action.op], Op::Done)
            };
            if matches {
                found.push(node_id);
            }
        }
        for transition in &graph[node_id].transitions {
            if transition.guard != graph.false_id() {
                queue.push_back(transition.target);
            }
        }
    }
    found
}

fn only_step(graph: &ProtoGraph, node: NodeId) -> &Transition {
    let transitions: Vec<_> = graph[node]
        .transitions
        .iter()
        .filter(|transition| transition.guard != graph.false_id())
        .collect();
    assert_eq!(
        transitions.len(),
        1,
        "TODO: meta lowering does not yet expand branching protocol cycles"
    );
    assert!(
        transitions[0].consumes_step,
        "protocol must be edge-contracted before meta lowering"
    );
    transitions[0]
}

// For now actual driver lowering handles one contracted control path. The meta
// construction itself already handles finite alternatives and unbounded pre phases.
fn protocol_shape(graph: &ProtoGraph, entry: NodeId, timing: &ProtocolTiming) -> ProtocolShape {
    let forks = reachable_markers(graph, entry, true);
    assert!(forks.len() <= 1, "only one fork per protocol is supported");
    let done = reachable_markers(graph, entry, false);
    assert_eq!(done.len(), 1, "each protocol must have exactly one done");
    let boundary = forks.first().copied().unwrap_or(done[0]);

    let mut pre = Vec::new();
    let mut node = entry;
    while node != boundary {
        assert!(!pre.contains(&node), "TODO: lower looping pre-phase control");
        pre.push(node);
        node = only_step(graph, node).target;
    }

    let mut post = Vec::new();
    if timing.post_cycles > 0 {
        node = boundary;
        while node != done[0] {
            assert!(!post.contains(&node), "post-phase cannot contain a cycle");
            post.push(node);
            node = only_step(graph, node).target;
        }
        assert_eq!(post.len(), timing.post_cycles);
    }

    assert_eq!(pre.len(), timing.pre_cycles.as_ref().unwrap()[0]);
    ProtocolShape { pre, post }
}

fn remap_expr(
    graph: &mut ProtoGraph,
    expr: ExprRef,
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> ExprRef {
    simple_transform_expr(&mut graph.expr_ctx, expr, |_ctx, candidate, _children| {
        substitutions.get(&candidate).copied()
    })
}

fn remap_op(
    graph: &mut ProtoGraph,
    op: Op,
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> Op {
    match op {
        Op::Assign(symbol, assignment) => Op::Assign(
            symbol,
            Assignment {
                dont_care: remap_expr(graph, assignment.dont_care, substitutions),
                concretes: assignment
                    .concretes
                    .into_iter()
                    .map(|(guard, rhs)| {
                        (
                            remap_expr(graph, guard, substitutions),
                            remap_expr(graph, rhs, substitutions),
                        )
                    })
                    .collect(),
            },
        ),
        Op::AssertEq(lhs, rhs) => Op::AssertEq(
            remap_expr(graph, lhs, substitutions),
            remap_expr(graph, rhs, substitutions),
        ),
        other => other,
    }
}

fn action_copy(
    graph: &mut ProtoGraph,
    old: NodeId,
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> NodeId {
    let old_node = graph[old].clone();
    let mut actions = Vec::new();
    for action in old_node.actions {
        if matches!(graph[action.op], Op::Done) {
            continue;
        }
        let op = remap_op(graph, graph[action.op].clone(), substitutions);
        let op = graph.o(op);
        let guard = remap_expr(graph, action.guard, substitutions);
        actions.push(Action::new(guard, op));
    }
    graph.n(Node {
        actions,
        transitions: Vec::new(),
    })
}

fn instance_substitutions(
    graph: &mut ProtoGraph,
    protocol: &Protocol,
    symbols: &SymbolTable,
    instance: usize,
) -> FxHashMap<ExprRef, ExprRef> {
    protocol
        .args
        .iter()
        .map(|arg| {
            let symbol = arg.symbol();
            let old = graph
                .symbol_expr(symbol)
                .expect("lowered protocol argument must have an expression");
            let width = old
                .get_bv_type(&graph.expr_ctx)
                .expect("protocol arguments must be bit vectors");
            let name = symbols[symbol].name();
            let new = graph
                .expr_ctx
                .bv_symbol(&format!("{name}#{instance}_{}", protocol.name), width);
            (old, new)
        })
        .collect()
}

fn choice_guard(
    graph: &mut ProtoGraph,
    node_choice: ExprRef,
    protocol: usize,
    protocol_count: usize,
    width: u32,
) -> ExprRef {
    if protocol_count == 1 {
        graph.true_id()
    } else {
        let value = graph.expr_ctx.bit_vec_val(protocol, width);
        graph.expr_ctx.equal(node_choice, value)
    }
}

fn lower_meta_driver_nfa(
    meta: MetaAutomaton,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
) -> (ProtoGraph, ExprRef) {
    assert!(!protocols.is_empty(), "a driver needs at least one protocol");
    assert_eq!(
        protocols.len(),
        meta.protocols.len(),
        "meta-automaton protocol count must match the lowered protocols"
    );

    let mut lowerer = Lowerer::with_expr_ctx(protocols[0].ctx.clone(), symbols, expr_ctx);
    let mut fragments = Vec::new();
    for protocol in &protocols {
        let fragment = lowerer.lower_protocol_fragment(protocol, true, false);
        contract_edges_from(&mut lowerer.ir, symbols, fragment.entry);
        fragments.push(fragment);
    }
    let shapes: Vec<_> = fragments
        .iter()
        .zip(&meta.protocols)
        .map(|(fragment, timing)| protocol_shape(&lowerer.ir, fragment.entry, timing))
        .collect();

    let width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    let node_choice = lowerer.ir.expr_ctx.bv_symbol("node_choice", width);
    let driver_nodes: Vec<_> = meta
        .nodes
        .iter()
        .map(|_| lowerer.ir.n(Node::empty()))
        .collect();

    // Fill every concrete node from the AND/OR units in its meta state.
    for (meta_id, meta_node) in meta.nodes.iter().enumerate() {
        let driver = driver_nodes[meta_id];

        for transaction in &meta_node.state.live {
            let protocol = transaction.protocol;
            let shape = &shapes[protocol];
            let index = meta.protocols[protocol].post_cycles - 1 - transaction.post_cycle;
            let substitutions = instance_substitutions(
                &mut lowerer.ir,
                &protocols[protocol],
                symbols,
                transaction.instance,
            );
            let copy = action_copy(&mut lowerer.ir, shape.post[index], &substitutions);
            lowerer.graft_contracted_entry(driver, copy, lowerer.ir.true_id());
        }

        match meta_node.state.frontier {
            Some(MetaFrontier::Choice { instance }) => {
                let mut choices = Vec::new();
                for protocol in 0..protocols.len() {
                    let shape = &shapes[protocol];
                    let substitutions = instance_substitutions(
                        &mut lowerer.ir,
                        &protocols[protocol],
                        symbols,
                        instance,
                    );
                    let copy = action_copy(&mut lowerer.ir, shape.pre[0], &substitutions);
                    let guard = choice_guard(
                        &mut lowerer.ir,
                        node_choice,
                        protocol,
                        protocols.len(),
                        width,
                    );
                    choices.push((copy, guard));
                }
                lowerer.graft_disjoint_contracted_entries(driver, &choices);
            }
            Some(MetaFrontier::Pre {
                     protocol,
                     instance,
                     elapsed,
                 }) => {
                let shape = &shapes[protocol];
                let substitutions = instance_substitutions(
                    &mut lowerer.ir,
                    &protocols[protocol],
                    symbols,
                    instance,
                );
                let copy = action_copy(&mut lowerer.ir, shape.pre[elapsed], &substitutions);
                lowerer.graft_contracted_entry(driver, copy, lowerer.ir.true_id());
            }
            None => {
                let done = lowerer.ir.o(Op::Done);
                lowerer
                    .ir
                    .push_action(driver, Action::new(lowerer.ir.true_id(), done));
            }
        }
    }

    // Meta edges already represent exactly one cycle.
    for (meta_id, meta_node) in meta.nodes.iter().enumerate() {
        for edge in &meta_node.edges {
            let mut guard = match meta_node.state.frontier.unwrap() {
                MetaFrontier::Choice { .. } => choice_guard(
                    &mut lowerer.ir,
                    node_choice,
                    edge.protocol,
                    protocols.len(),
                    width,
                ),
                MetaFrontier::Pre { .. } => lowerer.ir.true_id(),
            };

            // All currently active units must advance on this edge.
            for transaction in &meta_node.state.live {
                let mut ir = lowerer.ir.clone();
                let protocol = transaction.protocol;
                let index = meta.protocols[protocol].post_cycles - 1 - transaction.post_cycle;
                let step_guard = only_step(&ir, shapes[protocol].post[index]).guard;
                let substitutions = instance_substitutions(
                    &mut ir,
                    &protocols[protocol],
                    symbols,
                    transaction.instance,
                );
                let unit_guard = remap_expr(&mut ir, step_guard, &substitutions);
                guard = lowerer.ir.and_guard(guard, unit_guard);
            }

            let (protocol, instance, elapsed) = match meta_node.state.frontier.unwrap() {
                MetaFrontier::Choice { instance } => (edge.protocol, instance, 0),
                MetaFrontier::Pre {
                    protocol,
                    instance,
                    elapsed,
                } => (protocol, instance, elapsed),
            };
            let step = only_step(&lowerer.ir, shapes[protocol].pre[elapsed]);
            let step_guard = step.guard; // ExprRef is Copy — borrow of lowerer.ir ends here
            let substitutions = instance_substitutions(
                &mut lowerer.ir,
                &protocols[protocol],
                symbols,
                instance,
            );
            let unit_guard = remap_expr(&mut lowerer.ir, step_guard, &substitutions);

            guard = lowerer.ir.and_guard(guard, unit_guard);

            let mut transition = Transition::new(guard, driver_nodes[edge.target], true);
            transition.rotations = edge
                .rotations
                .iter()
                .map(|rotation| TransitionRotation {
                    protocol: meta.protocols[rotation.protocol].name.clone(),
                    amount: rotation.amount,
                })
                .collect();
            lowerer.ir.push_transition(driver_nodes[meta_id], transition);
        }
    }

    lowerer.ir.entry = driver_nodes[meta.entry];
    lowerer.ir.garbage_collect_unreachable();
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, node_choice)
}

/// Lower a bounded meta-automaton into a driver with one control node per meta node.
pub fn lower_bounded_driver_nfa(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
    fork_bound: usize,
) -> (ProtoGraph, MetaAutomaton, ExprRef) {
    assert!(!protocols.is_empty(), "a driver needs at least one protocol");

    let timings: Vec<_> = protocols
        .iter()
        .cloned()
        .map(|protocol| {
            let mut graph = lower_ast_to_ir(protocol, symbols);
            contract_edges(&mut graph, symbols);
            graph.garbage_collect_unreachable();
            analyze_protocol_timing(&graph)
        })
        .collect();
    let meta = bounded_driver_meta(timings, fork_bound);
    let (graph, node_choice) = lower_meta_driver_nfa(meta.clone(), protocols, symbols, expr_ctx);
    (graph, meta, node_choice)
}

/// Lower a meta-automaton into a driver with one control node per meta node.
/// Rotations remain transition annotations for later TS lowering.
pub fn lower_steady_driver_nfa(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
) -> (ProtoGraph, MetaAutomaton, ExprRef) {
    assert!(!protocols.is_empty(), "a driver needs at least one protocol");

    let timings: Vec<_> = protocols
        .iter()
        .cloned()
        .map(|protocol| {
            let mut graph = lower_ast_to_ir(protocol, symbols);
            contract_edges(&mut graph, symbols);
            graph.garbage_collect_unreachable();
            analyze_protocol_timing(&graph)
        })
        .collect();
    let meta = steady_driver_meta(timings);
    println!("{}", to_dot(&meta));
    let (graph, node_choice) = lower_meta_driver_nfa(meta.clone(), protocols, symbols, expr_ctx);
    (graph, meta, node_choice)
}

// TODO: Expand branching and looping pre-phase control into multiple concrete
// nodes for each meta continuation state.
// TODO: TS lowering must interpret banked argument names relative to the heads
// updated by TransitionRotation.
// TODO: OR merging must never create InternalAssertFalse between alternatives.

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::bounded_lowering::lower_bmc;
    use crate::ir::lowering::lower_ast_to_ir;
    use crate::ir::graphviz::to_dot_string;
    use insta::Settings;

    fn snap_selected(name: &str, filename: &str, selected: &[&str]) {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(&[filename], &mut handler, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let protocols = module
            .protos
            .into_iter()
            .filter(|protocol| selected.is_empty() || selected.contains(&protocol.name.as_str()))
            .collect();
        let (graph, _, _) = lower_steady_driver_nfa(protocols, &symbols, ExprContext::default());
        let dot = to_dot_string(&graph, &symbols);

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| insta::assert_snapshot!(name, dot));
    }

    #[test]
    fn steady_add_sub_d1() {
        snap_selected("steady_add_sub_d1", "../tests/alus/alu_d1.prot", &["add", "sub"]);
    }

    #[test]
    fn steady_add_sub_d2() {
        snap_selected("steady_add_sub_d2", "../tests/alus/alu_d2.prot", &["add", "sub"]);
    }

    #[test]
    fn steady_wishbone_read_reset() {
        snap_selected(
            "steady_wishbone_read_reset",
            "../tests/wishbone/wishbone.bi.prot",
            &["read", "reset"],
        );
    }
}
