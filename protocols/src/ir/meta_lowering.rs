use std::collections::VecDeque;

use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::{contract_edges, contract_edges_from};
use crate::ir::lowering::{Lowerer, lower_ast_to_ir};
use crate::ir::meta_automaton::{
    MetaAutomaton, MetaFrontier, MetaOutcome, bounded_driver_meta, steady_driver_meta,
};
use crate::ir::meta_timing::analyze_protocol_timing;
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation,
};

struct ProtocolShape {
    post: Vec<NodeId>,
    done: NodeId,
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
        "expected one transition in a linear phase"
    );
    assert!(
        transitions[0].consumes_step,
        "protocol must be edge-contracted before meta lowering"
    );
    transitions[0]
}

fn step_transitions(graph: &ProtoGraph, node: NodeId) -> Vec<Transition> {
    graph[node]
        .transitions
        .iter()
        .filter(|transition| transition.guard != graph.false_id())
        .cloned()
        .inspect(|transition| {
            assert!(
                transition.consumes_step,
                "protocol must be edge-contracted before meta lowering"
            );
        })
        .collect()
}

fn boundary_guard(
    graph: &mut ProtoGraph,
    node: NodeId,
    has_post_phase: bool,
    done: NodeId,
) -> ExprRef {
    let mut guards: Vec<_> = graph[node]
        .actions
        .iter()
        .filter_map(|action| {
            let is_boundary = if has_post_phase {
                matches!(graph[action.op], Op::Fork)
            } else {
                matches!(graph[action.op], Op::Done)
            };
            is_boundary.then_some(action.guard)
        })
        .collect();
    if has_post_phase {
        guards.extend(graph[node].transitions.iter().filter_map(|transition| {
            let target_is_fork = graph[transition.target]
                .actions
                .iter()
                .any(|action| matches!(graph[action.op], Op::Fork));
            target_is_fork.then_some(transition.guard)
        }));
    } else {
        guards.extend(
            graph[node]
                .transitions
                .iter()
                .filter_map(|transition| (transition.target == done).then_some(transition.guard)),
        );
    }
    guards
        .into_iter()
        .fold(graph.false_id(), |guard, next| graph.or_guard(guard, next))
}

fn protocol_shape(graph: &ProtoGraph, entry: NodeId, post_cycles: usize) -> ProtocolShape {
    let forks = reachable_markers(graph, entry, true);
    assert!(forks.len() <= 1, "only one fork per protocol is supported");
    let done = reachable_markers(graph, entry, false);
    assert_eq!(done.len(), 1, "each protocol must have exactly one done");
    let boundary = forks.first().copied().unwrap_or(done[0]);

    let mut node = boundary;
    let mut post = Vec::new();
    if post_cycles > 0 {
        while node != done[0] {
            assert!(!post.contains(&node), "post-phase cannot contain a cycle");
            post.push(node);
            node = only_step(graph, node).target;
        }
        assert_eq!(post.len(), post_cycles);
    }

    ProtocolShape {
        post,
        done: done[0],
    }
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

fn remap_op(graph: &mut ProtoGraph, op: Op, substitutions: &FxHashMap<ExprRef, ExprRef>) -> Op {
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
        .filter_map(|arg| {
            let symbol = arg.symbol();
            let old = graph.symbol_expr(symbol)?;
            let width = old
                .get_bv_type(&graph.expr_ctx)
                .expect("protocol arguments must be bit vectors");
            let name = symbols[symbol].name();
            let new = graph
                .expr_ctx
                .bv_symbol(&format!("{name}#{instance}_{}", protocol.name), width);
            Some((old, new))
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

fn reachable_pre_nodes(graph: &ProtoGraph, entry: NodeId) -> Vec<NodeId> {
    let mut nodes = Vec::new();
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::from([entry]);

    while let Some(node) = queue.pop_front() {
        if !seen.insert(node) {
            continue;
        }
        // The fork node starts the post-phase and the done node is only a
        // terminal marker. Neither is a concrete pre-phase frontier.
        let stops = graph[node]
            .actions
            .iter()
            .any(|action| matches!(graph[action.op], Op::Fork | Op::Done));
        if stops {
            continue;
        }
        nodes.push(node);
        for transition in step_transitions(graph, node) {
            if !graph[transition.target]
                .actions
                .iter()
                .any(|action| matches!(graph[action.op], Op::Done))
            {
                queue.push_back(transition.target);
            }
        }
    }
    nodes
}

/// Expand each meta state into the concrete protocol states
/// that can inhabit its pre-phase.
fn lower_exact_meta_driver_nfa(
    meta: MetaAutomaton,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
) -> (ProtoGraph, ExprRef, FxHashMap<NodeId, usize>) {
    assert!(
        !protocols.is_empty(),
        "a driver needs at least one protocol"
    );
    assert_eq!(protocols.len(), meta.protocols.len());

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
        .map(|(fragment, timing)| protocol_shape(&lowerer.ir, fragment.entry, timing.post_cycles))
        .collect();
    let pre_nodes: Vec<_> = fragments
        .iter()
        .map(|fragment| reachable_pre_nodes(&lowerer.ir, fragment.entry))
        .collect();

    let width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    let node_choice = lowerer.ir.expr_ctx.bv_symbol("node_choice", width);

    // None denotes a Choice/DONE meta state. Some(control) denotes a
    // concrete pre-phase control node for a Pre meta state.
    let mut driver_nodes: FxHashMap<(usize, Option<NodeId>), NodeId> = FxHashMap::default();
    for (meta_id, meta_node) in meta.nodes.iter().enumerate() {
        match meta_node.state.frontier {
            Some(MetaFrontier::Pre { protocol, .. }) => {
                for &control in &pre_nodes[protocol] {
                    driver_nodes.insert((meta_id, Some(control)), lowerer.ir.n(Node::empty()));
                }
            }
            Some(MetaFrontier::Choice { .. }) | None => {
                driver_nodes.insert((meta_id, None), lowerer.ir.n(Node::empty()));
            }
        }
    }

    // Install actions
    for (meta_id, meta_node) in meta.nodes.iter().enumerate() {
        let variants: Vec<_> = driver_nodes
            .iter()
            .filter_map(|(&(id, control), &node)| (id == meta_id).then_some((control, node)))
            .collect();

        for (control, driver) in variants {
            for transaction in &meta_node.state.live {
                let protocol = transaction.protocol;
                let index = meta.protocols[protocol].post_cycles - 1 - transaction.post_cycle;
                let substitutions = instance_substitutions(
                    &mut lowerer.ir,
                    &protocols[protocol],
                    symbols,
                    transaction.instance,
                );
                let copy = action_copy(
                    &mut lowerer.ir,
                    shapes[protocol].post[index],
                    &substitutions,
                );
                lowerer.graft_contracted_entry(driver, copy, lowerer.ir.true_id());
            }

            match (meta_node.state.frontier, control) {
                (Some(MetaFrontier::Choice { instance }), None) => {
                    let choices: Vec<_> = protocols
                        .iter()
                        .enumerate()
                        .map(|(protocol, ast)| {
                            let substitutions =
                                instance_substitutions(&mut lowerer.ir, ast, symbols, instance);
                            let copy = action_copy(
                                &mut lowerer.ir,
                                fragments[protocol].entry,
                                &substitutions,
                            );
                            let guard = choice_guard(
                                &mut lowerer.ir,
                                node_choice,
                                protocol,
                                protocols.len(),
                                width,
                            );
                            (copy, guard)
                        })
                        .collect();
                    lowerer.graft_disjoint_contracted_entries(driver, &choices);
                }
                (
                    Some(MetaFrontier::Pre {
                        protocol, instance, ..
                    }),
                    Some(control),
                ) => {
                    let substitutions = instance_substitutions(
                        &mut lowerer.ir,
                        &protocols[protocol],
                        symbols,
                        instance,
                    );
                    let copy = action_copy(&mut lowerer.ir, control, &substitutions);
                    lowerer.graft_contracted_entry(driver, copy, lowerer.ir.true_id());
                }
                (None, None) => {
                    let done = lowerer.ir.o(Op::Done);
                    lowerer
                        .ir
                        .push_action(driver, Action::new(lowerer.ir.true_id(), done));
                }
                _ => unreachable!("invalid exact meta variant"),
            }
        }
    }

    // Install one-cycle transitions for every concrete frontier variant.
    for (meta_id, meta_node) in meta.nodes.iter().enumerate() {
        let variants: Vec<_> = driver_nodes
            .iter()
            .filter_map(|(&(id, control), &node)| (id == meta_id).then_some((control, node)))
            .collect();

        for (control, driver) in variants {
            let frontier = meta_node.state.frontier;
            let (frontier_protocol, instance, source) = match (frontier, control) {
                (Some(MetaFrontier::Choice { instance }), None) => {
                    // A Choice node has one concrete source per selected
                    // protocol; the loop below supplies that source.
                    (None, instance, None)
                }
                (
                    Some(MetaFrontier::Pre {
                        protocol, instance, ..
                    }),
                    Some(control),
                ) => (Some(protocol), instance, Some(control)),
                _ => continue,
            };

            let edges = meta_node
                .edges
                .iter()
                .filter(|edge| frontier_protocol.is_none_or(|protocol| protocol == edge.protocol));

            for edge in edges {
                let protocol = edge.protocol;
                let source = source.unwrap_or(fragments[protocol].entry);
                let substitutions = instance_substitutions(
                    &mut lowerer.ir,
                    &protocols[protocol],
                    symbols,
                    instance,
                );
                let boundary = boundary_guard(
                    &mut lowerer.ir,
                    source,
                    meta.protocols[protocol].post_cycles > 0,
                    shapes[protocol].done,
                );
                let boundary = remap_expr(&mut lowerer.ir, boundary, &substitutions);
                let source_transitions = step_transitions(&lowerer.ir, source);

                let mut base_guard = if frontier_protocol.is_none() {
                    choice_guard(
                        &mut lowerer.ir,
                        node_choice,
                        protocol,
                        protocols.len(),
                        width,
                    )
                } else {
                    lowerer.ir.true_id()
                };

                for transaction in &meta_node.state.live {
                    let live_protocol = transaction.protocol;
                    let index =
                        meta.protocols[live_protocol].post_cycles - 1 - transaction.post_cycle;
                    let step_guard =
                        only_step(&lowerer.ir, shapes[live_protocol].post[index]).guard;
                    let live_substitutions = instance_substitutions(
                        &mut lowerer.ir,
                        &protocols[live_protocol],
                        symbols,
                        transaction.instance,
                    );
                    let step_guard = remap_expr(&mut lowerer.ir, step_guard, &live_substitutions);
                    base_guard = lowerer.ir.and_guard(base_guard, step_guard);
                }

                for step in source_transitions {
                    let step_guard = remap_expr(&mut lowerer.ir, step.guard, &substitutions);
                    let outcome_guard = if meta.protocols[protocol].pre_cycles.is_none() {
                        match edge.outcome {
                            MetaOutcome::Fork => lowerer.ir.and_guard(step_guard, boundary),
                            MetaOutcome::Continue => {
                                let not_boundary = lowerer.ir.not_guard(boundary);
                                lowerer.ir.and_guard(step_guard, not_boundary)
                            }
                        }
                    } else {
                        step_guard
                    };
                    let guard = lowerer.ir.and_guard(base_guard, outcome_guard);
                    if guard == lowerer.ir.false_id() {
                        continue;
                    }

                    let target_frontier = meta.nodes[edge.target].state.frontier;
                    let target_control = match (edge.outcome, target_frontier) {
                        (MetaOutcome::Continue, Some(MetaFrontier::Pre { .. })) => {
                            Some(step.target)
                        }
                        _ => None,
                    };
                    let target = *driver_nodes
                        .get(&(edge.target, target_control))
                        .unwrap_or_else(|| panic!("missing concrete meta target variant"));
                    let mut transition = Transition::new(guard, target, true);
                    transition.rotations = edge
                        .rotations
                        .iter()
                        .map(|rotation| TransitionRotation {
                            protocol: meta.protocols[rotation.protocol].name.clone(),
                            amount: rotation.amount,
                        })
                        .collect();
                    lowerer.ir.push_transition(driver, transition);
                }
            }
        }
    }

    let entry = *driver_nodes
        .get(&(meta.entry, None))
        .expect("meta entry must be a choice variant");
    let choice_instances: FxHashMap<_, _> = driver_nodes
        .iter()
        .filter_map(|(&(meta_id, control), &node)| {
            let Some(MetaFrontier::Choice { instance }) = meta.nodes[meta_id].state.frontier else {
                return None;
            };
            control.is_none().then_some((node, instance))
        })
        .collect();
    lowerer.ir.entry = entry;
    let node_map = lowerer.ir.garbage_collect_unreachable();
    lowerer.ir.simplify_all_exprs();
    let choice_instances = choice_instances
        .into_iter()
        .filter_map(|(node, instance)| Some((node_map.get(&node).copied()?, instance)))
        .collect();
    (lowerer.ir, node_choice, choice_instances)
}

/// Lower a bounded meta-automaton into a driver with one control node per meta node.
pub fn lower_bounded_driver_nfa(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
    fork_bound: usize,
) -> (ProtoGraph, MetaAutomaton, ExprRef) {
    assert!(
        !protocols.is_empty(),
        "a driver needs at least one protocol"
    );

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
    let (graph, node_choice, _) =
        lower_exact_meta_driver_nfa(meta.clone(), protocols, symbols, expr_ctx);
    (graph, meta, node_choice)
}

/// TODO: Explain the return type.
pub fn lower_steady_driver_nfa_with_choice_instances(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
) -> (ProtoGraph, MetaAutomaton, ExprRef, FxHashMap<NodeId, usize>) {
    assert!(
        !protocols.is_empty(),
        "a driver needs at least one protocol"
    );

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
    let (graph, node_choice, choice_instances) =
        lower_exact_meta_driver_nfa(meta.clone(), protocols, symbols, expr_ctx);
    (graph, meta, node_choice, choice_instances)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::determinize::determinized;
    use crate::ir::graphviz::to_dot_string;
    use crate::ir::meta_automaton::ProtocolTiming;
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
        let (graph, _, _, _) = lower_steady_driver_nfa_with_choice_instances(
            protocols,
            &symbols,
            ExprContext::default(),
        );
        let dot = to_dot_string(&graph, &symbols);

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| insta::assert_snapshot!(name, dot));
    }

    #[test]
    fn steady_add_sub_d1() {
        snap_selected(
            "steady_add_sub_d1",
            "../tests/alus/alu_d1.prot",
            &["add", "sub"],
        );
    }

    #[test]
    fn steady_add_sub_d2() {
        snap_selected(
            "steady_add_sub_d2",
            "../tests/alus/alu_d2.prot",
            &["add", "sub"],
        );
    }

    #[test]
    fn steady_counter_loop_lowering_does_not_panic() {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) =
            frontend(&["../tests/counters/counter.prot"], &mut handler, false).unwrap();
        let module = require_single_module(modules, &["../tests/counters/counter.prot"]).unwrap();
        let protocols = module.protos;
        let _ = lower_steady_driver_nfa_with_choice_instances(
            protocols,
            &symbols,
            ExprContext::default(),
        );
    }

    #[test]
    fn unbounded_pre_phase_steady_state_simple() {
        snap_selected(
            "unbounded_pre_phase_steady_state_simple_lowering",
            "../tests/meta/unbounded_pre_phase_steady_state_simple.prot",
            &["id", "w"],
        );
    }

    #[test]
    fn unbounded_pre_phase_steady_state_simple_is_finite_and_determinizable() {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(
            &["../tests/meta/unbounded_pre_phase_steady_state_simple.prot"],
            &mut handler,
            false,
        )
        .unwrap();
        let module = require_single_module(
            modules,
            &["../tests/meta/unbounded_pre_phase_steady_state_simple.prot"],
        )
        .unwrap();
        let (graph, _, _, _) = lower_steady_driver_nfa_with_choice_instances(
            module.protos,
            &symbols,
            ExprContext::default(),
        );

        assert!(
            graph.nodes().count() <= 16,
            "unexpected steady-state blowup"
        );
        let dfa = determinized(graph.clone(), &symbols);
        assert!(
            dfa.nodes().count() <= 64,
            "unexpected determinization blowup"
        );
    }

    #[test]
    fn steady_add_sub_d1_is_finite_and_determinizable() {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) =
            frontend(&["../tests/alus/alu_d1.prot"], &mut handler, false).unwrap();
        let module = require_single_module(modules, &["../tests/alus/alu_d1.prot"]).unwrap();
        let protocols = module
            .protos
            .into_iter()
            .filter(|protocol| matches!(protocol.name.as_str(), "add" | "sub"))
            .collect();
        let (graph, _, _, _) = lower_steady_driver_nfa_with_choice_instances(
            protocols,
            &symbols,
            ExprContext::default(),
        );
        assert!(
            graph.nodes().count() <= 8,
            "unexpected straight-line blowup"
        );
        let dfa = determinized(graph.clone(), &symbols);
        assert!(
            dfa.nodes().count() <= 16,
            "unexpected determinization blowup"
        );
    }

    fn lower_add_sub_with_meta(meta: MetaAutomaton) -> (ProtoGraph, SymbolTable) {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(
            &["../tests/meta/steady_state_add_sub_long_pre.prot"],
            &mut handler,
            false,
        )
        .unwrap();
        let module = require_single_module(
            modules,
            &["../tests/meta/steady_state_add_sub_long_pre.prot"],
        )
        .unwrap();
        let protocols = module.protos;
        let (graph, _, _) =
            lower_exact_meta_driver_nfa(meta, protocols, &symbols, ExprContext::default());
        (graph, symbols)
    }

    #[test]
    fn steady_state_add_sub_long_pre_bounded_meta_lowering() {
        let meta = steady_driver_meta(vec![
            ProtocolTiming::new("add", vec![2], 1),
            ProtocolTiming::new("sub", vec![2], 1),
        ]);
        let (graph, symbols) = lower_add_sub_with_meta(meta);
        assert!(
            graph.nodes().count() <= 32,
            "unexpected steady-state blowup"
        );
        let dfa = determinized(graph.clone(), &symbols);
        assert!(
            dfa.nodes().count() <= 128,
            "unexpected determinization blowup"
        );
        insta::assert_snapshot!(to_dot_string(&graph, &symbols));
    }

    #[test]
    fn steady_state_add_sub_long_pre_unbounded_meta_lowering() {
        let meta = steady_driver_meta(vec![
            ProtocolTiming::unbounded("add", 1),
            ProtocolTiming::unbounded("sub", 1),
        ]);
        let (graph, symbols) = lower_add_sub_with_meta(meta);
        assert!(
            graph.nodes().count() <= 32,
            "unexpected steady-state blowup"
        );
        let dfa = determinized(graph.clone(), &symbols);
        assert!(
            dfa.nodes().count() <= 128,
            "unexpected determinization blowup"
        );
        insta::assert_snapshot!(to_dot_string(&graph, &symbols));
    }

    #[test]
    fn steady_wishbone_read_reset() {
        snap_selected(
            "steady_wishbone_read_reset",
            "../examples/wishbone/wishbone.prot",
            &["read", "reset"],
        );
    }

    #[test]
    fn steady_wishbone() {
        snap_selected(
            "steady_wishbone",
            "../examples/wishbone/wishbone.prot",
            &[
                "read",
                "reset",
                "write",
                "idle_no_cycle",
                "idle_continue_cycle",
            ],
        );
    }
}
