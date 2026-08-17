use rustc_hash::FxHashMap;

pub type ProtocolId = usize;
pub type MetaNodeId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolTiming {
    pub name: String,
    /// Every cycle at which this protocol may reach its phase boundary, counted
    /// from its selection. The boundary is done when `post_cycles` is zero.
    /// `None` means that it may reach the boundary in any cycle or continue forever.
    pub pre_cycles: Option<Vec<usize>>,
    /// Fixed post-phase lifetime, including the fork cycle. Zero means that the
    /// protocol has no fork and therefore no post-phase.
    pub post_cycles: usize,
}

impl ProtocolTiming {
    pub fn new(name: impl Into<String>, pre_cycles: Vec<usize>, post_cycles: usize) -> Self {
        Self {
            name: name.into(),
            pre_cycles: Some(pre_cycles),
            post_cycles,
        }
    }

    pub fn unbounded(name: impl Into<String>, post_cycles: usize) -> Self {
        Self {
            name: name.into(),
            pre_cycles: None,
            post_cycles,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LiveTransaction {
    pub protocol: ProtocolId,
    pub instance: usize,
    /// Counts down from ProtocolTiming::post_cycles.
    /// The final post-phase cycle is zero.
    pub post_cycle: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MetaFrontier {
    /// The driver has not yet selected the next protocol.
    Choice { instance: usize },
    /// A selected protocol is somewhere in its pre-phase.
    Pre {
        protocol: ProtocolId,
        instance: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MetaState {
    pub live: Vec<LiveTransaction>,
    /// Bounded trees have no frontier after their final fork.
    pub frontier: Option<MetaFrontier>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaOutcome {
    Select,
    /// Reaches fork, or done for a protocol with no post-phase.
    Fork,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForkTiming {
    /// These exact pre-phase lengths all produce the same meta successor.
    Exact(Vec<usize>),
    /// Every length at least this value has the same drained context.
    AtLeast(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BankRotation {
    pub protocol: ProtocolId,
    pub amount: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstanceShift {
    pub protocol: ProtocolId,
    pub amount: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaEdge {
    pub protocol: ProtocolId,
    pub outcome: MetaOutcome,
    pub target: MetaNodeId,
    pub instance_shifts: Vec<InstanceShift>,
    pub rotations: Vec<BankRotation>,
    pub fork_timing: Option<ForkTiming>,
    /// Number of cycles by which the meta-level post transactions advance.
    pub advance_cycles: usize,
    /// Global display-superscript normalization, not a bank update.
    canonical_shift: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaNode {
    pub state: MetaState,
    pub edges: Vec<MetaEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaAutomaton {
    pub protocols: Vec<ProtocolTiming>,
    pub nodes: Vec<MetaNode>,
    pub entry: MetaNodeId,
    pub bank_counts: Vec<usize>,
}

#[derive(Debug)]
struct Successor {
    state: MetaState,
    protocol: ProtocolId,
    outcome: MetaOutcome,
    fork_timing: Option<ForkTiming>,
    advance_cycles: usize,
}

fn validate_and_normalize(mut protocols: Vec<ProtocolTiming>) -> Vec<ProtocolTiming> {
    assert!(
        !protocols.is_empty(),
        "a meta-automaton needs at least one protocol"
    );

    for protocol in &mut protocols {
        assert!(!protocol.name.is_empty(), "protocol names cannot be empty");
        if let Some(pre_cycles) = &mut protocol.pre_cycles {
            assert!(
                !pre_cycles.is_empty(),
                "{} must have at least one possible pre-phase length",
                protocol.name
            );
            assert!(
                pre_cycles.iter().all(|cycles| *cycles > 0),
                "{} has a zero pre-phase length",
                protocol.name
            );
            pre_cycles.sort_unstable();
            pre_cycles.dedup();
        }
    }

    for left in 0..protocols.len() {
        for right in left + 1..protocols.len() {
            assert_ne!(
                protocols[left].name, protocols[right].name,
                "duplicate protocol name {}",
                protocols[left].name
            );
        }
    }

    protocols
}

fn advance_live(live: &[LiveTransaction], cycles: usize) -> Vec<LiveTransaction> {
    live.iter()
        .filter_map(|transaction| {
            if transaction.post_cycle < cycles {
                None
            } else {
                Some(LiveTransaction {
                    post_cycle: transaction.post_cycle - cycles,
                    ..*transaction
                })
            }
        })
        .collect()
}

fn drain_cycles(live: &[LiveTransaction]) -> usize {
    live.iter()
        .map(|transaction| transaction.post_cycle + 1)
        .max()
        .unwrap_or(0)
}

fn relevant_fork_timings(pre_cycles: Option<&[usize]>, drain: usize) -> Vec<(usize, ForkTiming)> {
    match pre_cycles {
        Some(lengths) => {
            let mut groups: Vec<(usize, Vec<usize>)> = Vec::new();
            for &length in lengths {
                let effective = length.min(drain);
                if let Some((_, grouped)) = groups.iter_mut().find(|(prior, _)| *prior == effective)
                {
                    grouped.push(length);
                } else {
                    groups.push((effective, vec![length]));
                }
            }
            groups
                .into_iter()
                .map(|(effective, lengths)| (effective, ForkTiming::Exact(lengths)))
                .collect()
        }
        None if drain == 0 => vec![(0, ForkTiming::AtLeast(1))],
        None => (1..=drain)
            .map(|cycles| {
                let timing = if cycles == drain {
                    ForkTiming::AtLeast(cycles)
                } else {
                    ForkTiming::Exact(vec![cycles])
                };
                (cycles, timing)
            })
            .collect(),
    }
}

fn fork_successor(
    mut live: Vec<LiveTransaction>,
    protocols: &[ProtocolTiming],
    protocol: ProtocolId,
    instance: usize,
    introduce_next_choice: bool,
) -> MetaState {
    if protocols[protocol].post_cycles > 0 {
        live.push(LiveTransaction {
            protocol,
            instance,
            post_cycle: protocols[protocol].post_cycles - 1,
        });
    }
    live.sort_by_key(|transaction| (transaction.instance, transaction.protocol));

    MetaState {
        live,
        frontier: introduce_next_choice.then(|| MetaFrontier::Choice {
            instance: instance.checked_add(1).expect("instance number overflow"),
        }),
    }
}

fn successors(
    state: &MetaState,
    protocols: &[ProtocolTiming],
    introduce_next_choice: bool,
) -> Vec<Successor> {
    let Some(frontier) = state.frontier else {
        return Vec::new();
    };
    let mut result = Vec::new();

    match frontier {
        MetaFrontier::Choice { instance } => {
            for protocol in 0..protocols.len() {
                result.push(Successor {
                    state: MetaState {
                        live: state.live.clone(),
                        frontier: Some(MetaFrontier::Pre { protocol, instance }),
                    },
                    protocol,
                    outcome: MetaOutcome::Select,
                    fork_timing: None,
                    advance_cycles: 0,
                });
            }
        }
        MetaFrontier::Pre { protocol, instance } => {
            let drain = drain_cycles(&state.live);
            for (advance_cycles, fork_timing) in
                relevant_fork_timings(protocols[protocol].pre_cycles.as_deref(), drain)
            {
                result.push(Successor {
                    state: fork_successor(
                        advance_live(&state.live, advance_cycles),
                        protocols,
                        protocol,
                        instance,
                        introduce_next_choice,
                    ),
                    protocol,
                    outcome: MetaOutcome::Fork,
                    fork_timing: Some(fork_timing),
                    advance_cycles,
                });
            }
        }
    }

    assert!(
        !result.is_empty(),
        "pre-phase timing has no possible successor"
    );
    result
}

fn canonicalize(mut state: MetaState) -> (MetaState, usize) {
    let live_min = state
        .live
        .iter()
        .map(|transaction| transaction.instance)
        .min();
    let frontier_min = state.frontier.map(|frontier| match frontier {
        MetaFrontier::Choice { instance } | MetaFrontier::Pre { instance, .. } => instance,
    });
    let shift = live_min
        .into_iter()
        .chain(frontier_min)
        .min()
        .expect("steady-state nodes cannot be empty");

    for transaction in &mut state.live {
        transaction.instance -= shift;
    }
    state.frontier = state.frontier.map(|frontier| match frontier {
        MetaFrontier::Choice { instance } => MetaFrontier::Choice {
            instance: instance - shift,
        },
        MetaFrontier::Pre { protocol, instance } => MetaFrontier::Pre {
            protocol,
            instance: instance - shift,
        },
    });

    (state, shift)
}

fn push_bounded_node(
    nodes: &mut Vec<MetaNode>,
    protocols: &[ProtocolTiming],
    state: MetaState,
    forks: usize,
    fork_bound: usize,
) -> MetaNodeId {
    let id = nodes.len();
    nodes.push(MetaNode {
        state: state.clone(),
        edges: Vec::new(),
    });

    if state.frontier.is_none() {
        return id;
    }

    for successor in successors(&state, protocols, forks + 1 < fork_bound) {
        let next_forks = forks + usize::from(successor.outcome == MetaOutcome::Fork);
        let target = push_bounded_node(nodes, protocols, successor.state, next_forks, fork_bound);
        nodes[id].edges.push(MetaEdge {
            protocol: successor.protocol,
            outcome: successor.outcome,
            target,
            instance_shifts: Vec::new(),
            rotations: Vec::new(),
            fork_timing: successor.fork_timing,
            advance_cycles: successor.advance_cycles,
            canonical_shift: 0,
        });
    }
    id
}

fn bank_counts(protocol_count: usize, nodes: &[MetaNode]) -> Vec<usize> {
    let mut counts = vec![0; protocol_count];
    for node in nodes {
        let mut state_counts = vec![0; protocol_count];
        for transaction in &node.state.live {
            state_counts[transaction.protocol] += 1;
        }
        match node.state.frontier {
            Some(MetaFrontier::Choice { .. }) => {
                for count in &mut state_counts {
                    *count += 1;
                }
            }
            Some(MetaFrontier::Pre { protocol, .. }) => state_counts[protocol] += 1,
            None => {}
        }
        for protocol in 0..protocol_count {
            counts[protocol] = counts[protocol].max(state_counts[protocol]);
        }
    }
    counts
}

fn instance_shifts(state: &MetaState, protocol_count: usize, amount: usize) -> Vec<InstanceShift> {
    if amount == 0 {
        return Vec::new();
    }

    let mut actual = vec![false; protocol_count];
    for transaction in &state.live {
        actual[transaction.protocol] = true;
    }
    if let Some(MetaFrontier::Pre { protocol, .. }) = state.frontier {
        actual[protocol] = true;
    }
    actual
        .into_iter()
        .enumerate()
        .filter_map(|(protocol, actual)| actual.then_some(InstanceShift { protocol, amount }))
        .collect()
}

// TODO: not sure if this is totally correct.
fn validate_fifo_edge(graph: &MetaAutomaton, source: MetaNodeId, edge: &MetaEdge) {
    let source = &graph.nodes[source].state;
    let target = &graph.nodes[edge.target].state;
    let raw_target_live = |protocol, instance, post_cycle| {
        target.live.iter().any(|transaction| {
            transaction.protocol == protocol
                && transaction.instance + edge.canonical_shift == instance
                && transaction.post_cycle == post_cycle
        })
    };

    match edge.outcome {
        MetaOutcome::Select => {
            assert_eq!(edge.advance_cycles, 0);
            assert!(edge.fork_timing.is_none());
            for transaction in &source.live {
                assert!(raw_target_live(
                    transaction.protocol,
                    transaction.instance,
                    transaction.post_cycle
                ));
            }
            assert!(matches!(
                target.frontier,
                Some(MetaFrontier::Pre { protocol, instance })
                    if protocol == edge.protocol
                        && Some(instance + edge.canonical_shift)
                            == source.frontier.map(|frontier| match frontier {
                                MetaFrontier::Choice { instance } => instance,
                                MetaFrontier::Pre { .. } => unreachable!(),
                            })
            ));
        }
        MetaOutcome::Fork => {
            assert!(edge.fork_timing.is_some());
            for transaction in &source.live {
                if transaction.post_cycle >= edge.advance_cycles {
                    assert!(raw_target_live(
                        transaction.protocol,
                        transaction.instance,
                        transaction.post_cycle - edge.advance_cycles
                    ));
                }
            }
            let MetaFrontier::Pre { protocol, instance } = source.frontier.unwrap() else {
                panic!("fork edge must leave a pre node")
            };
            assert_eq!(protocol, edge.protocol);
            if graph.protocols[protocol].post_cycles > 0 {
                assert!(raw_target_live(
                    protocol,
                    instance,
                    graph.protocols[protocol].post_cycles - 1
                ));
            }
        }
    }
}

fn add_rotations(graph: &mut MetaAutomaton) {
    for source in 0..graph.nodes.len() {
        let edges = graph.nodes[source].edges.clone();
        for (edge_index, edge) in edges.iter().enumerate() {
            validate_fifo_edge(graph, source, edge);
            let rotations = edge
                .instance_shifts
                .iter()
                .filter_map(|shift| {
                    let amount = shift.amount % graph.bank_counts[shift.protocol];
                    (amount != 0).then_some(BankRotation {
                        protocol: shift.protocol,
                        amount,
                    })
                })
                .collect();
            graph.nodes[source].edges[edge_index].rotations = rotations;
        }
    }
}

pub fn bounded_driver_meta(protocols: Vec<ProtocolTiming>, fork_bound: usize) -> MetaAutomaton {
    assert!(fork_bound > 0, "the fork bound must be nonzero");
    let protocols = validate_and_normalize(protocols);
    let mut nodes = Vec::new();
    let entry = push_bounded_node(
        &mut nodes,
        &protocols,
        MetaState {
            live: Vec::new(),
            frontier: Some(MetaFrontier::Choice { instance: 0 }),
        },
        0,
        fork_bound,
    );
    let bank_counts = bank_counts(protocols.len(), &nodes);
    MetaAutomaton {
        protocols,
        nodes,
        entry,
        bank_counts,
    }
}

pub fn steady_driver_meta(protocols: Vec<ProtocolTiming>) -> MetaAutomaton {
    let protocols = validate_and_normalize(protocols);
    let entry_state = MetaState {
        live: Vec::new(),
        frontier: Some(MetaFrontier::Choice { instance: 0 }),
    };
    let mut nodes = vec![MetaNode {
        state: entry_state.clone(),
        edges: Vec::new(),
    }];
    let mut states = FxHashMap::default();
    states.insert(entry_state, 0);
    let mut cursor = 0;

    while cursor < nodes.len() {
        let state = nodes[cursor].state.clone();
        let mut edges = Vec::new();
        for successor in successors(&state, &protocols, true) {
            let (canonical, canonical_shift) = canonicalize(successor.state);
            let instance_shifts = instance_shifts(&canonical, protocols.len(), canonical_shift);
            let target = if let Some(target) = states.get(&canonical) {
                *target
            } else {
                let target = nodes.len();
                states.insert(canonical.clone(), target);
                nodes.push(MetaNode {
                    state: canonical,
                    edges: Vec::new(),
                });
                target
            };
            edges.push(MetaEdge {
                protocol: successor.protocol,
                outcome: successor.outcome,
                target,
                instance_shifts,
                rotations: Vec::new(),
                fork_timing: successor.fork_timing,
                advance_cycles: successor.advance_cycles,
                canonical_shift,
            });
        }
        nodes[cursor].edges = edges;
        cursor += 1;
    }

    let bank_counts = bank_counts(protocols.len(), &nodes);
    let mut graph = MetaAutomaton {
        protocols,
        nodes,
        entry: 0,
        bank_counts,
    };
    add_rotations(&mut graph);
    graph
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::meta_graphviz::to_dot;
    use insta::Settings;
    use std::path::Path;

    fn snap(name: &str, content: &str) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    fn add_sub_depth_one() -> Vec<ProtocolTiming> {
        vec![
            ProtocolTiming::new("A", vec![1], 1),
            ProtocolTiming::new("S", vec![1], 1),
        ]
    }

    #[test]
    fn steady_state_varying_post_lengths() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1], 1),
            ProtocolTiming::new("S", vec![1], 2),
        ];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_varying_post_lengths", &to_dot(&graph))
        // println!("{}", to_dot(&graph));
    }

    #[test]
    fn steady_state_d1() {
        let inputs = vec![ProtocolTiming::new("A", vec![1], 1)];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_add_d1", &to_dot(&graph))
    }

    #[test]
    fn steady_state_d2() {
        let inputs = vec![ProtocolTiming::new("A", vec![1], 2)];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_add_d2", &to_dot(&graph))
    }

    #[test]
    fn steady_state_varying_pre_lengths() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1, 2], 1),
            ProtocolTiming::new("S", vec![1], 1),
        ];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_varying_pre_lengths", &to_dot(&graph))
    }

    #[test]
    fn steady_state_varying_pre_and_post_lengths() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1, 2], 1),
            ProtocolTiming::new("S", vec![1], 2),
        ];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_varying_pre_and_post_lengths", &to_dot(&graph))
    }

    #[test]
    fn bounded_add_sub() {
        let graph = bounded_driver_meta(add_sub_depth_one(), 2);
        snap("bounded_add_sub", &to_dot(&graph))
    }

    #[test]
    fn steady_add_sub_d1() {
        let graph = steady_driver_meta(add_sub_depth_one());

        snap("steady_add_sub_d1", &to_dot(&graph))
    }

    #[test]
    fn finite_pre_phase_choices_steady_state() {
        let graph = steady_driver_meta(vec![
            ProtocolTiming::new("ADD", vec![1, 2], 2),
            ProtocolTiming::new("SUB", vec![1], 1),
        ]);

        snap("finite_pre_phase_choices_steady_state", &to_dot(&graph))
    }

    #[test]
    fn unbounded_pre_phase_steady_state() {
        let graph = steady_driver_meta(vec![
            ProtocolTiming::new("ADD", vec![1], 2),
            ProtocolTiming::unbounded("WAIT", 1),
        ]);

        snap("unbounded_pre_phase_steady_state", &to_dot(&graph))
    }

    #[test]
    fn bounded_tree_for_unbounded_pre() {
        let graph = bounded_driver_meta(
            vec![
                ProtocolTiming::new("ADD", vec![1], 2),
                ProtocolTiming::unbounded("WAIT", 1),
            ],
            2,
        );

        snap("bounded_tree_for_unbounded_pre", &to_dot(&graph))
    }

    #[test]
    #[should_panic]
    fn rejects_empty_protocol_set() {
        let _ = steady_driver_meta(Vec::new());
    }

    #[test]
    fn accepts_protocol_without_post_phase() {
        let graph = steady_driver_meta(vec![ProtocolTiming::new("ADD", vec![1], 0)]);
        assert!(graph.nodes.iter().all(|node| node.state.live.is_empty()));
    }

    #[test]
    #[should_panic]
    fn rejects_empty_pre_lengths() {
        let _ = steady_driver_meta(vec![ProtocolTiming::new("ADD", Vec::new(), 1)]);
    }

    #[test]
    #[should_panic]
    fn rejects_zero_pre_length() {
        let _ = steady_driver_meta(vec![ProtocolTiming::new("ADD", vec![0, 1], 1)]);
    }

    #[test]
    #[should_panic]
    fn rejects_duplicate_names() {
        let _ = steady_driver_meta(vec![
            ProtocolTiming::new("ADD", vec![1], 1),
            ProtocolTiming::new("ADD", vec![1], 1),
        ]);
    }

    #[test]
    #[should_panic]
    fn rejects_zero_fork_bound() {
        let _ = bounded_driver_meta(add_sub_depth_one(), 0);
    }
}
