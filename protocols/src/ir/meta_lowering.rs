use std::collections::VecDeque;

use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::{contract_edges, contract_edges_from};
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer, lower_ast_to_ir};
use crate::ir::meta_automaton::{
    ForkTiming, MetaAutomaton, MetaFrontier, MetaOutcome, ProtocolTiming, steady_driver_meta,
};
use crate::ir::meta_timing::analyze_protocol_timing;
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Cursor {
    Pre(NodeId, usize),
    Post(NodeId),
}

#[derive(Clone)]
struct ExpandedPre {
    entry: NodeId,
    boundaries: Vec<(NodeId, usize)>,
}

fn reachable_marker(graph: &ProtoGraph, entry: NodeId, want_fork: bool) -> Vec<NodeId> {
    let mut found = Vec::new();
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::from([entry]);
    while let Some(node_id) = queue.pop_front() {
        if !seen.insert(node_id) {
            continue;
        }
        for action in &graph[node_id].actions {
            let matches = if want_fork {
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

fn copy_node(
    graph: &mut ProtoGraph,
    old: NodeId,
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> NodeId {
    let old_node = graph[old].clone();
    let mut actions = Vec::new();
    for action in old_node.actions {
        // Transaction-local done must not finish the steady-state driver.
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

fn timing_matches(timing: &ForkTiming, elapsed: usize) -> bool {
    match timing {
        ForkTiming::Exact(lengths) => lengths.contains(&elapsed),
        ForkTiming::AtLeast(first) => elapsed >= *first,
    }
}

// Copy one selected pre-phase. Pre cycles are time-expanded only far enough to
// distinguish its meta successors; an unbounded pre-phase then saturates.
fn expand_pre(
    graph: &mut ProtoGraph,
    fragment: &LoweredFragmentInfo,
    timing: &ProtocolTiming,
    meta_edges: &[crate::ir::meta_automaton::MetaEdge],
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> ExpandedPre {
    let forks = reachable_marker(graph, fragment.entry, true);
    assert!(forks.len() <= 1, "only one fork per protocol is supported");
    let done = reachable_marker(graph, fragment.entry, false);
    assert_eq!(done.len(), 1, "each protocol must have exactly one done");
    let boundary = forks.first().copied().unwrap_or(done[0]);

    let saturation = timing.pre_cycles.is_none().then(|| {
        meta_edges
            .iter()
            .find_map(|edge| match edge.fork_timing {
                Some(ForkTiming::AtLeast(first)) => Some(first),
                _ => None,
            })
            .expect("unbounded pre-phase needs a saturated meta edge")
    });

    let start = Cursor::Pre(fragment.entry, 0);
    let mut copies = FxHashMap::default();
    let entry = copy_node(graph, fragment.entry, substitutions);
    copies.insert(start, entry);
    let mut queue = VecDeque::from([start]);
    let mut boundaries = Vec::new();

    while let Some(cursor) = queue.pop_front() {
        let (old, elapsed, before_boundary) = match cursor {
            Cursor::Pre(old, elapsed) => (old, elapsed, true),
            Cursor::Post(old) => (old, 0, false),
        };
        let new = copies[&cursor];
        if before_boundary && old == boundary {
            boundaries.push((new, elapsed));
        }

        let transitions = graph[old].transitions.clone();
        for transition in transitions {
            if transition.guard == graph.false_id() {
                continue;
            }
            assert!(
                transition.consumes_step,
                "protocol fragments must be edge-contracted"
            );

            let next_cursor = if before_boundary && old == boundary {
                Cursor::Post(transition.target)
            } else if before_boundary {
                let next = elapsed.checked_add(1).expect("pre-phase length overflow");
                Cursor::Pre(
                    transition.target,
                    saturation.map_or(next, |cap| next.min(cap)),
                )
            } else {
                Cursor::Post(transition.target)
            };
            let target = if let Some(target) = copies.get(&next_cursor) {
                *target
            } else {
                let old_target = match next_cursor {
                    Cursor::Pre(old, _) | Cursor::Post(old) => old,
                };
                let target = copy_node(graph, old_target, substitutions);
                copies.insert(next_cursor, target);
                queue.push_back(next_cursor);
                target
            };
            let guard = remap_expr(graph, transition.guard, substitutions);
            graph.push_transition(new, Transition::new(guard, target, true));
        }
    }

    assert!(
        !boundaries.is_empty(),
        "pre-phase cannot reach its boundary"
    );
    for (_, elapsed) in &boundaries {
        assert!(meta_edges.iter().any(|edge| {
            edge.outcome == MetaOutcome::Fork
                && timing_matches(edge.fork_timing.as_ref().unwrap(), *elapsed)
        }));
    }
    ExpandedPre { entry, boundaries }
}

fn bank_substitutions(
    graph: &mut ProtoGraph,
    protocol: &Protocol,
    symbols: &SymbolTable,
    bank: usize,
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
            let name = symbols.full_name_from_symbol_id(&symbol);
            let new = graph.expr_ctx.bv_symbol(&format!("{name}#{bank}"), width);
            (old, new)
        })
        .collect()
}

/// Lower a steady-state driver meta-automaton into an NFA-style `ProtoGraph`.
/// Run `determinized` afterwards to make the AND concurrency explicit.
///
/// Bank rotations on meta back-edges are intentionally not lowered yet.
pub fn lower_steady_driver_nfa(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
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
    let meta = steady_driver_meta(timings);

    let mut lowerer = Lowerer::with_expr_ctx(protocols[0].ctx.clone(), symbols, expr_ctx);
    let mut fragments = Vec::new();
    for protocol in &protocols {
        let fragment = lowerer.lower_protocol_fragment(protocol, true, false);
        contract_edges_from(&mut lowerer.ir, symbols, fragment.entry);
        fragments.push(fragment);
    }

    let width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    let node_choice = lowerer.ir.expr_ctx.bv_symbol("node_choice", width);

    let mut controls = vec![None; meta.nodes.len()];
    for (id, node) in meta.nodes.iter().enumerate() {
        if matches!(node.state.frontier, Some(MetaFrontier::Choice { .. })) {
            controls[id] = Some(lowerer.ir.n(Node::empty()));
        }
    }

    let mut expanded = vec![None; meta.nodes.len()];
    for (id, node) in meta.nodes.iter().enumerate() {
        let Some(MetaFrontier::Pre { protocol, instance }) = node.state.frontier else {
            continue;
        };
        let bank = instance % meta.bank_counts[protocol];
        let substitutions =
            bank_substitutions(&mut lowerer.ir, &protocols[protocol], symbols, bank);
        expanded[id] = Some(expand_pre(
            &mut lowerer.ir,
            &fragments[protocol],
            &meta.protocols[protocol],
            &node.edges,
            &substitutions,
        ));
    }

    // Choice states are OR units selected by the shared per-cycle node choice.
    for (id, node) in meta.nodes.iter().enumerate() {
        let Some(control) = controls[id] else {
            continue;
        };
        let mut choices = Vec::new();
        for edge in &node.edges {
            assert_eq!(edge.outcome, MetaOutcome::Select);
            let value = lowerer.ir.expr_ctx.bit_vec_val(edge.protocol, width);
            let guard = if protocols.len() == 1 {
                lowerer.ir.true_id()
            } else {
                lowerer.ir.expr_ctx.equal(node_choice, value)
            };
            choices.push((expanded[edge.target].as_ref().unwrap().entry, guard));
        }
        lowerer.graft_disjoint_contracted_entries(control, &choices);
    }

    // A boundary and the next choice occur in the same cycle, so graft rather
    // than add a transition between them.
    for (id, node) in meta.nodes.iter().enumerate() {
        let Some(expanded_pre) = &expanded[id] else {
            continue;
        };
        for &(boundary, elapsed) in &expanded_pre.boundaries {
            let edge = node
                .edges
                .iter()
                .find(|edge| {
                    edge.outcome == MetaOutcome::Fork
                        && timing_matches(edge.fork_timing.as_ref().unwrap(), elapsed)
                })
                .expect("boundary timing must have a meta successor");
            let target = controls[edge.target].expect("steady-state boundary must reach a choice");
            let first_new_transition = lowerer.ir[boundary].transitions.len();
            lowerer.graft_contracted_entry(boundary, target, lowerer.ir.true_id());
            let rotations: Vec<_> = edge
                .rotations
                .iter()
                .map(|rotation| TransitionRotation {
                    protocol: meta.protocols[rotation.protocol].name.clone(),
                    amount: rotation.amount,
                })
                .collect();
            for transition in
                &mut lowerer.ir.node_mut(boundary).transitions[first_new_transition..]
            {
                transition.rotations.extend(rotations.clone());
            }
        }
    }

    lowerer.ir.entry = controls[meta.entry].expect("meta entry must be a choice");
    lowerer.ir.garbage_collect_unreachable();
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, meta, node_choice)
}

// TODO: Apply the meta-edge bank rotations when lowering back-edges.
// TODO: OR merging must never create InternalAssertFalse between alternatives.

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
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
        let (graph, _, _) =
            lower_steady_driver_nfa(protocols, &symbols, ExprContext::default());
        let dot = to_dot_string(&graph, &symbols);

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| insta::assert_snapshot!(name, dot));
    }

    fn snap(name: &str, filename: &str) {
        snap_selected(name, filename, &[]);
    }

    #[test]
    fn add_d1_driver_graphviz() {
        snap("meta_driver_add_d1", "../tests/adders/add_d1.prot");
    }

    #[test]
    fn add_d0_driver_graphviz() {
        snap(
            "meta_driver_add_d0",
            "../tests/adders/adder_d0/add_d0.prot",
        );
    }

    #[test]
    fn add_sub_d1_driver_graphviz() {
        snap_selected(
            "meta_driver_add_sub_d1",
            "../tests/alus/alu_d1.prot",
            &["add", "sub"],
        );
    }

    #[test]
    fn add_sub_d2_driver_graphviz() {
        snap_selected(
            "meta_driver_add_sub_d2",
            "../tests/alus/alu_d2.prot",
            &["add", "sub"],
        );
    }
}
