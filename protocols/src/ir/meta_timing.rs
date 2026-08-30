use std::collections::{BTreeSet, VecDeque};

use rustc_hash::FxHashSet;

use crate::ir::meta_automaton::{MetaAutomaton, ProtocolTiming, steady_driver_meta};
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph};

#[derive(Clone, Copy)]
enum Marker {
    Fork,
    Done,
}

// TODO: This assumes that we don't have unreachable nodes hanging around that haven't
// been pruned yet.
fn marker_nodes(graph: &ProtoGraph, marker: Marker) -> Vec<NodeId> {
    let mut found = Vec::new();
    for (node_id, node) in graph.nodes() {
        for action in &node.actions {
            let matches = match marker {
                Marker::Fork => matches!(graph[action.op], Op::Fork),
                Marker::Done => matches!(graph[action.op], Op::Done),
            };
            if matches {
                found.push(node_id);
            }
        }
    }

    found
}

// Returns None when a cycle occurs before the target.
fn path_lengths(graph: &ProtoGraph, start: NodeId, target: NodeId) -> Option<BTreeSet<usize>> {
    let mut stack = VecDeque::from([(start, 0, FxHashSet::default())]);
    let mut lengths = BTreeSet::new();

    while let Some((node, length, mut path)) = stack.pop_back() {
        if node == target {
            lengths.insert(length);
            continue;
        }
        if !path.insert(node) {
            return None;
        }

        let transitions: Vec<_> = graph[node]
            .transitions
            .iter()
            .filter(|transition| transition.guard != graph.false_id())
            .collect();
        assert!(
            !transitions.is_empty(),
            "a path in protocol {} terminates before it reaching a fork",
            graph.name
        );

        for transition in transitions {
            // This analysis is deliberately defined only on post-contraction IR.
            assert!(
                transition.consumes_step,
                "protocol {} must be edge-contracted before timing analysis",
                graph.name
            );
            stack.push_back((transition.target, length + 1, path.clone()));
        }
    }

    Some(lengths)
}

/// Extract the timing summary used by the driver meta-automaton.
///
/// Restrictions for now:
/// - `graph` is already edge-contracted;
/// - there are zero or one fork actions and exactly one done action;
/// - every fork-to-done path is acyclic and has the same positive length;
/// - if there is an entry-to-fork cycle, we assume the pre-phase unbounded.
pub fn analyze_protocol_timing(graph: &ProtoGraph) -> ProtocolTiming {
    let forks = marker_nodes(graph, Marker::Fork);
    assert!(
        forks.len() <= 1,
        "protocol {} cannot contain more than one fork",
        graph.name
    );
    let done_nodes = marker_nodes(graph, Marker::Done);
    assert_eq!(
        done_nodes.len(),
        1,
        "protocol {} must contain exactly one done",
        graph.name
    );
    let done = done_nodes[0];

    let (pre_boundary, post_cycles) = if let Some(&fork) = forks.first() {
        let post_lengths = path_lengths(graph, fork, done)
            .unwrap_or_else(|| panic!("protocol {} has a cycle after fork", graph.name));
        assert_eq!(
            post_lengths.len(),
            1,
            "all fork-to-done paths in protocol {} must have the same length",
            graph.name
        );
        let post_cycles = *post_lengths.iter().next().unwrap();
        assert!(
            post_cycles > 0,
            "protocol {} must step at least once after fork",
            graph.name
        );
        (fork, post_cycles)
    } else {
        // With no fork, done is the implicit end of the pre-phase.
        (done, 0)
    };

    match path_lengths(graph, graph.entry, pre_boundary) {
        Some(pre_cycles) => ProtocolTiming::new(
            graph.name.clone(),
            pre_cycles.into_iter().collect(),
            post_cycles,
        ),
        None => ProtocolTiming::unbounded(graph.name.clone(), post_cycles),
    }
}

/// Analyze post-contraction protocol graphs and construct their steady-state
/// driver meta-automaton in the same order as the input slice.
pub fn steady_driver_meta_from_protocols(protocols: &[ProtoGraph]) -> MetaAutomaton {
    let timings = protocols.iter().map(analyze_protocol_timing).collect();
    steady_driver_meta(timings)
}

// TODO: Expand the meta-automaton into a ProtoGraph and add bank rotations.
// TODO: OR-unit merging must not introduce InternalAssertFalse between the
// alternative protocol fragments; those alternatives are not concurrent.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::edge_contract::contract_edges;
    use crate::ir::lowering::lower_ast_to_ir;

    fn contracted_protocols(filename: &str) -> Vec<ProtoGraph> {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();

        module
            .protos
            .into_iter()
            .map(|protocol| {
                let mut graph = lower_ast_to_ir(protocol, &symbols);
                contract_edges(&mut graph, &symbols);
                graph.garbage_collect_unreachable();
                graph
            })
            .collect()
    }

    fn assert_timing(graph: &ProtoGraph, pre_cycles: Option<Vec<usize>>, post_cycles: usize) {
        let timing = analyze_protocol_timing(graph);
        assert_eq!(timing.name, graph.name);
        assert_eq!(timing.pre_cycles, pre_cycles);
        assert_eq!(timing.post_cycles, post_cycles);
    }

    #[test]
    fn extracts_add_d1_timing() {
        let graphs = contracted_protocols("../tests/adders/add_d1.prot");
        assert_eq!(graphs.len(), 1);
        assert_timing(&graphs[0], Some(vec![1]), 1);
    }

    #[test]
    fn extracts_counter_timing() {
        let graphs = contracted_protocols("../tests/counters/counter.prot");
        assert_eq!(graphs.len(), 2);
        for graph in &graphs {
            assert_timing(graph, None, 1);
        }
    }

    #[test]
    fn extracts_alu_d1_timings() {
        let graphs = contracted_protocols("../tests/alus/alu_d1.prot");
        assert_eq!(graphs.len(), 4);
        for graph in &graphs {
            assert_timing(graph, Some(vec![1]), 1);
        }
    }

    #[test]
    fn extracts_add_d0_timings() {
        let graphs = contracted_protocols("../tests/adders/adder_d0/add_d0.prot");
        assert_eq!(graphs.len(), 4);
        for graph in &graphs {
            assert_timing(graph, Some(vec![1]), 0);
        }

        let meta = steady_driver_meta_from_protocols(&graphs);
        assert!(meta.nodes.iter().all(|node| node.state.post_phase.is_empty()));
    }
}
