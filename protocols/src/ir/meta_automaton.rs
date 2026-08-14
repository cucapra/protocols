use std::collections::HashMap;

pub type ProtocolId = usize;
pub type MetaNodeId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolTiming {
    pub name: String,
    /// Every cycle at which this protocol may fork, counted from its selection.
    /// `None` means that it may fork in any cycle and may continue forever.
    pub pre_cycles: Option<Vec<usize>>,
    /// Fixed post-phase lifetime, including the fork cycle.
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
    /// A selected protocol has consumed `elapsed` pre-phase cycles without forking.
    Pre {
        protocol: ProtocolId,
        instance: usize,
        elapsed: usize,
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
    Fork,
    Continue,
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
}

fn validate_and_normalize(mut protocols: Vec<ProtocolTiming>) -> Vec<ProtocolTiming> {
    assert!(
        !protocols.is_empty(),
        "a meta-automaton needs at least one protocol"
    );

    for protocol in &mut protocols {
        assert!(!protocol.name.is_empty(), "protocol names cannot be empty");
        assert!(
            protocol.post_cycles > 0,
            "{} must have a nonzero post-phase bound",
            protocol.name
        );
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

fn advance_live(live: &[LiveTransaction]) -> Vec<LiveTransaction> {
    live.iter()
        .filter_map(|transaction| {
            if transaction.post_cycle == 0 {
                None
            } else {
                Some(LiveTransaction {
                    post_cycle: transaction.post_cycle - 1,
                    ..*transaction
                })
            }
        })
        .collect()
}

fn fork_successor(
    mut live: Vec<LiveTransaction>,
    protocols: &[ProtocolTiming],
    protocol: ProtocolId,
    instance: usize,
    introduce_next_choice: bool,
) -> MetaState {
    live.push(LiveTransaction {
        protocol,
        instance,
        post_cycle: protocols[protocol].post_cycles - 1,
    });
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
    let advanced = advance_live(&state.live);
    let mut result = Vec::new();

    match frontier {
        MetaFrontier::Choice { instance } => {
            for protocol in 0..protocols.len() {
                let timings = protocols[protocol].pre_cycles.as_deref();
                if timings.is_none_or(|timings| timings.binary_search(&1).is_ok()) {
                    result.push(Successor {
                        state: fork_successor(
                            advanced.clone(),
                            protocols,
                            protocol,
                            instance,
                            introduce_next_choice,
                        ),
                        protocol,
                        outcome: MetaOutcome::Fork,
                    });
                }
                if timings.is_none_or(|timings| timings.last().copied().unwrap() > 1) {
                    result.push(Successor {
                        state: MetaState {
                            live: advanced.clone(),
                            frontier: Some(MetaFrontier::Pre {
                                protocol,
                                instance,
                                elapsed: 1,
                            }),
                        },
                        protocol,
                        outcome: MetaOutcome::Continue,
                    });
                }
            }
        }
        MetaFrontier::Pre {
            protocol,
            instance,
            elapsed,
        } => {
            let next = elapsed.checked_add(1).expect("pre-phase length overflow");
            let timings = protocols[protocol].pre_cycles.as_deref();
            if timings.is_none_or(|timings| timings.binary_search(&next).is_ok()) {
                result.push(Successor {
                    state: fork_successor(
                        advanced.clone(),
                        protocols,
                        protocol,
                        instance,
                        introduce_next_choice,
                    ),
                    protocol,
                    outcome: MetaOutcome::Fork,
                });
            }
            if timings.is_none_or(|timings| timings.last().copied().unwrap() > next) {
                result.push(Successor {
                    state: MetaState {
                        live: advanced,
                        frontier: Some(MetaFrontier::Pre {
                            protocol,
                            instance,
                            // All unbounded wait cycles have the same control shape.
                            elapsed: if timings.is_none() { elapsed } else { next },
                        }),
                    },
                    protocol,
                    outcome: MetaOutcome::Continue,
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
        MetaFrontier::Pre {
            protocol,
            instance,
            elapsed,
        } => MetaFrontier::Pre {
            protocol,
            instance: instance - shift,
            elapsed,
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
        // An unbounded pre-phase eventually drains all surrounding post-phase
        // transactions. Continuing after that produces this exact state again.
        let target = if successor.outcome == MetaOutcome::Continue && successor.state == state {
            id
        } else {
            push_bounded_node(nodes, protocols, successor.state, next_forks, fork_bound)
        };
        nodes[id].edges.push(MetaEdge {
            protocol: successor.protocol,
            outcome: successor.outcome,
            target,
            instance_shifts: Vec::new(),
            rotations: Vec::new(),
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

fn validate_fifo_edge(graph: &MetaAutomaton, source: MetaNodeId, edge: &MetaEdge) {
    let target = &graph.nodes[edge.target].state;
    let raw_target_live = |protocol, instance, post_cycle| {
        target.live.iter().any(|transaction| {
            transaction.protocol == protocol
                && transaction.instance + edge.canonical_shift == instance
                && transaction.post_cycle == post_cycle
        })
    };

    for transaction in &graph.nodes[source].state.live {
        if transaction.post_cycle > 0 {
            assert!(
                raw_target_live(
                    transaction.protocol,
                    transaction.instance,
                    transaction.post_cycle - 1
                ),
                "canonicalization reordered a live transaction"
            );
        }
    }

    if let Some(MetaFrontier::Pre {
        protocol, instance, ..
    }) = graph.nodes[source].state.frontier
    {
        match edge.outcome {
            MetaOutcome::Continue => assert!(matches!(
                target.frontier,
                Some(MetaFrontier::Pre {
                    protocol: target_protocol,
                    instance: target_instance,
                    ..
                }) if target_protocol == protocol
                    && target_instance + edge.canonical_shift == instance
            )),
            MetaOutcome::Fork => assert!(raw_target_live(
                protocol,
                instance,
                graph.protocols[protocol].post_cycles - 1
            )),
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
    let mut states = HashMap::from([(entry_state, 0)]);
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

fn format_state(graph: &MetaAutomaton, state: &MetaState) -> String {
    let mut parts: Vec<String> = state
        .live
        .iter()
        .map(|transaction| {
            format!(
                "{}<SUB>{}</SUB><SUP>({})</SUP>",
                escape_html(&graph.protocols[transaction.protocol].name),
                transaction.post_cycle,
                transaction.instance
            )
        })
        .collect();

    if let Some(frontier) = state.frontier {
        parts.push(match frontier {
            MetaFrontier::Choice { instance } => format!("E<SUP>({instance})</SUP>"),
            MetaFrontier::Pre {
                protocol,
                instance,
                elapsed,
            } => {
                let phase = if graph.protocols[protocol].pre_cycles.is_none() {
                    "pre".to_string()
                } else {
                    format!("pre[{elapsed}]")
                };
                format!(
                    "{}<SUB>{}</SUB><SUP>({})</SUP>",
                    escape_html(&graph.protocols[protocol].name),
                    phase,
                    instance
                )
            }
        });
    }

    if parts.is_empty() {
        "DONE".to_string()
    } else {
        parts.join(" ∧ ")
    }
}

fn escape_html(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

pub fn to_dot(graph: &MetaAutomaton) -> String {
    let mut output = String::from(
        "digraph \"driver_meta\" {\n  rankdir=LR;\n  node [shape=box];\n  entry [shape=plain,label=\"ENTRY\"];\n",
    );
    output.push_str(&format!("  entry -> node{};\n", graph.entry));

    for (node_id, node) in graph.nodes.iter().enumerate() {
        output.push_str(&format!(
            "  node{node_id} [label=<{}>];\n",
            format_state(graph, &node.state)
        ));
        for edge in &node.edges {
            let outcome = match edge.outcome {
                MetaOutcome::Fork => "forks",
                MetaOutcome::Continue => "continues",
            };
            let mut label = format!(
                "{} {outcome}",
                escape_html(&graph.protocols[edge.protocol].name)
            );
            if !edge.rotations.is_empty() {
                let rotations = edge
                    .rotations
                    .iter()
                    .map(|rotation| {
                        let name = escape_html(&graph.protocols[rotation.protocol].name);
                        if rotation.amount == 1 {
                            format!("R<SUB>{name}</SUB>")
                        } else {
                            format!("R<SUB>{name}</SUB><SUP>{}</SUP>", rotation.amount)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                label.push_str(&format!(" / {rotations}"));
            }
            output.push_str(&format!(
                "  node{node_id} -> node{} [label=<{}>];\n",
                edge.target, label
            ));
        }
    }
    output.push_str("}\n");
    output
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use insta::Settings;
    use super::*;

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
    fn steady_state_varying_lengths() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1], 1),
            ProtocolTiming::new("S", vec![1], 2),
        ];
        let graph = steady_driver_meta(inputs);

        println!("{}", to_dot(&graph));
    }

    #[test]
    fn steady_state_d1() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1], 1),
        ];
        let graph = steady_driver_meta(inputs);

        println!("{}", to_dot(&graph));
    }

    #[test]
    fn steady_state_d2() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1], 2),
        ];
        let graph = steady_driver_meta(inputs);

        println!("{}", to_dot(&graph));
    }

    #[test]
    fn steady_state_varying_pre_lengths() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![1, 2], 1),
            ProtocolTiming::new("S", vec![1], 1),
        ];
        let graph = steady_driver_meta(inputs);

        println!("{}", to_dot(&graph));
    }

    #[test]
    fn bounded_add_sub_is_a_literal_tree() {
        let graph = bounded_driver_meta(add_sub_depth_one(), 2);
        println!("{}", to_dot(&graph));
    }

    #[test]
    fn steady_add_sub_reuses_nodes_and_rotates_banks() {
        let graph = steady_driver_meta(add_sub_depth_one());

        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.bank_counts, vec![2, 2]);
        let dot = to_dot(&graph);
        println!("{}", dot);
    }

    #[test]
    fn switching_protocols_rotates_the_newly_selected_protocol() {
        let graph = steady_driver_meta(add_sub_depth_one());
        for (source_protocol, selected_protocol) in [(0, 1), (1, 0)] {
            let source = graph
                .nodes
                .iter()
                .find(|node| {
                    node.state
                        .live
                        .iter()
                        .any(|transaction| transaction.protocol == source_protocol)
                })
                .unwrap();
            let edge = source
                .edges
                .iter()
                .find(|edge| edge.protocol == selected_protocol)
                .unwrap();
            assert_eq!(
                edge.instance_shifts,
                vec![InstanceShift {
                    protocol: selected_protocol,
                    amount: 1,
                }]
            );
            assert_eq!(
                edge.rotations,
                vec![BankRotation {
                    protocol: selected_protocol,
                    amount: 1,
                }]
            );
        }
    }

    #[test]
    fn finite_pre_phase_alternatives_reach_steady_state() {
        let graph = steady_driver_meta(vec![
            ProtocolTiming::new("ADD", vec![1, 2], 2),
            ProtocolTiming::new("SUB", vec![1], 1),
        ]);

        assert!(graph.nodes.len() > 3);
        assert!(graph.nodes.len() < 20);
        println!("{}", to_dot(&graph));
    }

    #[test]
    fn unbounded_pre_phase_exhausts_post_contexts_then_self_loops() {
        let graph = steady_driver_meta(vec![
            ProtocolTiming::new("ADD", vec![1], 2),
            ProtocolTiming::unbounded("WAIT", 1),
        ]);

        println!("{}", to_dot(&graph));
    }

    #[test]
    #[should_panic]
    fn rejects_empty_protocol_set() {
        let _ = steady_driver_meta(Vec::new());
    }

    #[test]
    #[should_panic]
    fn rejects_zero_post_bound() {
        let _ = steady_driver_meta(vec![ProtocolTiming::new("ADD", vec![1], 0)]);
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

    #[test]
    fn bounded_tree_for_unbounded_pre() {
        let graph = bounded_driver_meta(
            vec![
                ProtocolTiming::new("ADD", vec![1], 2),
                ProtocolTiming::unbounded("WAIT", 1),
            ],
            2,
        );

        println!("{}", to_dot(&graph));
    }
}
