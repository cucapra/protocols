use rustc_hash::FxHashMap;

pub type ProtocolId = usize;
pub type MetaNodeId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolTiming {
    pub name: String,
    /// The sorted, non-repeating list in ascending order of possible numbers of cycles required
    /// until the protocol forks.
    /// `None` means that it may reach the boundary in any number of cycles.
    /// 0 means the protocol immediately forks (which is disallowed by the well-formedness rules)
    pub pre_cycles: Option<Vec<usize>>,
    /// The lifetime of the protocol in cycles, including the fork cycle.
    /// If zero, the protocol has no fork and therefore no post-phase.
    pub post_cycles: usize,
}

// TODO: I feel like these impl helpers are simply unnecessary
// and can be replaced with direct struct constructions.
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
pub struct PostPhaseTransaction {
    pub protocol: ProtocolId,
    /// Which execution of the protocol this is.
    /// Logical instance number. Physical bank selection is performed by the
    /// lowered transition system using the protocol's FIFO head.
    pub instance: usize,
    /// Counts down from ProtocolTiming::post_cycles.
    /// The final post-phase cycle is zero.
    pub post_cycle: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// There can only ever be one protocol in the 'pre' phase (by the structured concurrency
/// guarantees of the language), or else we have just forked, and we have not
/// disambiguated which protocol we're running, in which case we're in the `Choice` version.
pub enum PrePhase {
    /// The driver has not yet selected the next protocol.
    Choice { instance: usize },
    /// A selected protocol is somewhere in its pre-phase.
    Pre {
        protocol: ProtocolId,
        instance: usize,
        elapsed: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MetaState {
    /// The things in the post-phase
    pub post_phase: Vec<PostPhaseTransaction>,
    /// See the definition of `PrePhase`. Note the optional,
    /// since the frontier can also be empty if we're just doing the
    /// bounded (not steady-state) construction
    pub pre_phase: Option<PrePhase>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// When we're in the pre-phase, we may transition
/// into a Fork state or continue in the pre-phase.
pub enum MetaOutcome {
    Fork,
    Continue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForkTiming {
    /// These exact pre-phase lengths all produce the same meta successor.
    Exact(Vec<usize>),
    /// Every length at least this value has the same drained context.
    AtLeast(usize),
}

// A rotation is how much to rotate the instance numbers to reuse
// an existing node. This is per-protocol. For a given protocol with N instances/banks,
// the remapping of every instance number `i` is `i + amount (mod N)`
// TODO: Standardize on Bank or Instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BankRotation {
    pub protocol: ProtocolId,
    pub amount: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaEdge {
    // At every edge, a protocol (the one in the pre-phase) is forking, or continuing.
    pub protocol: ProtocolId,
    // Did we choose to fork or continue?
    pub outcome: MetaOutcome,
    pub target: MetaNodeId,
    // what rotations are required before transitioning to `target`
    pub rotations: Vec<BankRotation>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaNode {
    pub state: MetaState,
    pub edges: Vec<MetaEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaAutomaton {
    // `protocols` and `bank_counts` are parallel arrays.
    // `bank_counts[i]` are the number of banks required for `protocols[i]`
    pub protocols: Vec<ProtocolTiming>,
    pub bank_counts: Vec<usize>,
    pub nodes: Vec<MetaNode>,
    pub entry: MetaNodeId,
}

#[derive(Debug)]
/// A temporary structure describing an edge to a new state.
struct Successor {
    /// The state produced by taking the edge
    state: MetaState,
    /// Which protocol and by what outcome was the edge taken
    protocol: ProtocolId,
    outcome: MetaOutcome,
}

// need >0 protocols as input with nonempty names
// need >0 pre-phase lengths, and all should be > 0
// there should be no duplicate protocol names
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

fn fork_successor(
    mut post_phase_txs: Vec<PostPhaseTransaction>,
    protocols: &[ProtocolTiming],
    protocol: ProtocolId,
    instance: usize,
    introduce_next_choice: bool,
) -> MetaState {
    if protocols[protocol].post_cycles > 0 {
        post_phase_txs.push(PostPhaseTransaction {
            protocol,
            instance,
            post_cycle: protocols[protocol].post_cycles - 1,
        });
    }
    post_phase_txs.sort_by_key(|transaction| (transaction.instance, transaction.protocol));

    MetaState {
        post_phase: post_phase_txs,
        pre_phase: introduce_next_choice.then(|| PrePhase::Choice {
            instance: instance.checked_add(1).expect("instance number overflow"),
        }),
    }
}

/// Compute all one-cycle transitions from a state
fn successors(
    state: &MetaState,
    protocols: &[ProtocolTiming],
    introduce_next_choice: bool,
) -> Vec<Successor> {
    // if there is nothing in the pre-phase, we have no successor states
    // TODO: why?
    let Some(pre_phase) = state.pre_phase else {
        return Vec::new();
    };
    let mut result = Vec::new();

    let choices: Vec<_> = match pre_phase {
        // Every protocol is a choice, with the same instance number and 0 cycles have elapsed
        // (Since we're currently in the first cycle of their life).
        PrePhase::Choice { instance } => (0..protocols.len())
            .map(|protocol| (protocol, instance, 0))
            .collect(),
        // There is only one protocol in the pre-phase, and it has existing bank and cycles
        // elapsed data
        PrePhase::Pre {
            protocol,
            instance,
            elapsed,
        } => vec![(protocol, instance, elapsed)],
    };

    for (protocol, instance, elapsed) in choices {
        let next = elapsed + 1;
        let timing = protocols[protocol].pre_cycles.as_deref();

        // we can fork if the number of cycles elapsed meets one of the pre_cycles lengths.
        let can_fork = timing.is_none_or(|lengths| lengths.binary_search(&next).is_ok());

        // we can continue if the number of cycles elapsed is less than one of the pre_cycles lengths
        let can_continue = timing.is_none_or(|lengths| lengths.last().copied().unwrap() > next);

        // everything in the post-phase needs to be advanced 1 cycle
        // TODO: can we do this in place
        let advanced: Vec<PostPhaseTransaction> = state.post_phase.iter()
            // drop the transaction if its
            .filter_map(|transaction| {
                if transaction.post_cycle == 0 {
                    None
                } else {
                    Some(PostPhaseTransaction {
                        post_cycle: transaction.post_cycle - 1,
                        ..*transaction
                    })
                }
            })
            .collect();

        if can_fork {
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
        if can_continue {
            result.push(Successor {
                state: MetaState {
                    post_phase: advanced,
                    pre_phase: Some(PrePhase::Pre {
                        protocol,
                        instance,
                        elapsed: if timing.is_none() { 1 } else { next },
                    }),
                },
                protocol,
                outcome: MetaOutcome::Continue,
            });
        }
    }

    assert!(
        !result.is_empty(),
        "pre-phase timing has no possible successor"
    );
    result
}


fn canonicalize(mut state: MetaState, protocol_count: usize) -> MetaState {
    // We assume that if an equivalent state up to renumbering by shifts is available
    // it will be 0-ed. so, we calculate the 0-ed version of this state and return it.

    // find the minimum instance per-protocol
    let mut shifts = vec![None; protocol_count];
    for transaction in &state.post_phase {
        shifts[transaction.protocol] = Some(
            shifts[transaction.protocol]
                .unwrap_or(transaction.instance)
                .min(transaction.instance),
        );
    }
    if let Some(PrePhase::Pre {
        protocol, instance, ..
    }) = state.pre_phase
    {
        shifts[protocol] = Some(shifts[protocol].unwrap_or(instance).min(instance));
    }


    // reset every transactions by their minimum (essentially re-zero everything)
    for transaction in &mut state.post_phase {
        transaction.instance -= shifts[transaction.protocol].unwrap();
    }
    state.pre_phase = state.pre_phase.map(|frontier| match frontier {
        PrePhase::Choice { instance } => {
            let global_shift = shifts.iter().flatten().copied().min().unwrap_or(instance);
            PrePhase::Choice {
                instance: instance - global_shift,
            }
        }
        PrePhase::Pre {
            protocol,
            instance,
            elapsed,
        } => PrePhase::Pre {
            protocol,
            instance: instance - shifts[protocol].unwrap(),
            elapsed,
        },
    });

    state
}

/// Determine the FIFO-head movement needed to map `source` onto `target`.
/// The subtraction is deliberately wrapping: rotations are interpreted
/// modulo the eventual bank count, and the bank count is not known until all
/// canonical nodes have been constructed.
fn rotations_between(
    source: &MetaState,
    target: &MetaState,
    protocol_count: usize,
) -> Vec<BankRotation> {
    let mut result = Vec::new();
    for protocol in 0..protocol_count {
        let mut source_instances: Vec<_> = source
            .post_phase
            .iter()
            .filter(|transaction| transaction.protocol == protocol)
            .map(|transaction| (transaction.instance, transaction.post_cycle))
            .collect();
        let mut target_instances: Vec<_> = target
            .post_phase
            .iter()
            .filter(|transaction| transaction.protocol == protocol)
            .map(|transaction| (transaction.instance, transaction.post_cycle))
            .collect();
        if let Some(PrePhase::Pre {
            protocol: frontier_protocol,
            instance,
            elapsed: _,
        }) = source.pre_phase
            && frontier_protocol == protocol
        {
            source_instances.push((instance, usize::MAX));
        }
        if let Some(PrePhase::Pre {
            protocol: frontier_protocol,
            instance,
            elapsed: _,
        }) = target.pre_phase
            && frontier_protocol == protocol
        {
            target_instances.push((instance, usize::MAX));
        }
        source_instances.sort_unstable();
        target_instances.sort_unstable();
        assert_eq!(
            source_instances.len(),
            target_instances.len(),
            "protocol {protocol} changed instance multiplicity while canonicalizing"
        );
        let Some((&(source_instance, _), &(target_instance, _))) =
            source_instances.first().zip(target_instances.first())
        else {
            continue;
        };
        let amount = source_instance.wrapping_sub(target_instance);
        assert!(
            source_instances.iter().zip(&target_instances).all(
                |(&(source_instance, source_cycle), &(target_instance, target_cycle))| {
                    source_cycle == target_cycle
                        && source_instance.wrapping_sub(amount) == target_instance
                }
            ),
            "no single instance shift maps all live instances of protocol {protocol}"
        );
        if amount != 0 {
            result.push(BankRotation { protocol, amount });
        }
    }
    result
}

fn push_bounded_node(
    nodes: &mut Vec<MetaNode>,
    protocols: &[ProtocolTiming],
    state: MetaState,
    forks_so_far: usize,
    fork_bound: usize,
) -> MetaNodeId {
    // create a new node
    let id = nodes.len();
    nodes.push(MetaNode {
        state: state.clone(),
        edges: Vec::new(),
    });

    if state.pre_phase.is_none() {
        return id;
    }

    for successor in successors(&state, protocols, forks_so_far + 1 < fork_bound) {
        let next_forks = forks_so_far + usize::from(successor.outcome == MetaOutcome::Fork);
        let target = if successor.outcome == MetaOutcome::Continue && successor.state == state {
            id
        } else {
            push_bounded_node(nodes, protocols, successor.state, next_forks, fork_bound)
        };
        nodes[id].edges.push(MetaEdge {
            protocol: successor.protocol,
            outcome: successor.outcome,
            target,
            rotations: Vec::new(),
        });
    }
    id
}

fn bank_counts(protocol_count: usize, nodes: &[MetaNode]) -> Vec<usize> {
    let mut counts = vec![0; protocol_count];
    for node in nodes {
        let mut state_counts = vec![0; protocol_count];
        for transaction in &node.state.post_phase {
            state_counts[transaction.protocol] += 1;
        }
        match node.state.pre_phase {
            Some(PrePhase::Choice { .. }) => {
                for count in &mut state_counts {
                    *count += 1;
                }
            }
            Some(PrePhase::Pre { protocol, .. }) => state_counts[protocol] += 1,
            None => {}
        }
        for protocol in 0..protocol_count {
            counts[protocol] = counts[protocol].max(state_counts[protocol]);
        }
    }
    counts
}

fn validate_fifo_edge(graph: &MetaAutomaton, source: MetaNodeId, edge: &MetaEdge) {
    let source = &graph.nodes[source].state;
    let target = &graph.nodes[edge.target].state;
    let rotation_for = |protocol: ProtocolId| {
        edge.rotations
            .iter()
            .find(|rotation| rotation.protocol == protocol)
            .map_or(0, |rotation| rotation.amount)
    };
    let target_live = |protocol: ProtocolId, instance: usize, post_cycle: usize| {
        let count = graph.bank_counts[protocol].max(1);
        target.post_phase.iter().any(|transaction| {
            transaction.protocol == protocol
                && transaction.instance
                    == (instance % count + count - rotation_for(protocol) % count) % count
                && transaction.post_cycle == post_cycle
        })
    };

    for transaction in &source.post_phase {
        if transaction.post_cycle > 0 {
            assert!(target_live(
                transaction.protocol,
                transaction.instance,
                transaction.post_cycle - 1
            ));
        }
    }
    let (protocol, instance) = match source.pre_phase.unwrap() {
        PrePhase::Choice { instance } => (edge.protocol, instance),
        PrePhase::Pre {
            protocol, instance, ..
        } => {
            assert_eq!(protocol, edge.protocol);
            (protocol, instance)
        }
    };

    match edge.outcome {
        MetaOutcome::Fork => {
            if graph.protocols[protocol].post_cycles > 0 {
                assert!(target_live(
                    protocol,
                    instance,
                    graph.protocols[protocol].post_cycles - 1
                ));
            }
        }
        MetaOutcome::Continue => {
            let shift = rotation_for(protocol);
            assert!(matches!(
                target.pre_phase,
                Some(PrePhase::Pre {
                    protocol: target_protocol,
                    instance: target_instance,
                    ..
                }) if target_protocol == protocol
                    && target_instance
                        == (instance + graph.bank_counts[protocol].max(1)
                            - shift % graph.bank_counts[protocol].max(1))
                            % graph.bank_counts[protocol].max(1)
            ));
        }
    }
}

fn add_rotations(graph: &mut MetaAutomaton) {
    for source in 0..graph.nodes.len() {
        let edges = graph.nodes[source].edges.clone();
        for (edge_index, edge) in edges.iter().enumerate() {
            validate_fifo_edge(graph, source, edge);
            let rotations = edge
                .rotations
                .iter()
                .filter_map(|shift| {
                    let amount = shift.amount % graph.bank_counts[shift.protocol].max(1);
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
    let initial_state = MetaState {
        post_phase: Vec::new(),
        pre_phase: Some(PrePhase::Choice { instance: 0 }),
    };
    let entry = push_bounded_node(&mut nodes, &protocols, initial_state, 0, fork_bound);
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
        post_phase: Vec::new(),
        pre_phase: Some(PrePhase::Choice { instance: 0 }),
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
            let canonical = canonicalize(successor.state.clone(), protocols.len());
            let rotations = rotations_between(&successor.state, &canonical, protocols.len());
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
                rotations,
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

    fn add_depth_one() -> Vec<ProtocolTiming> {
        vec![ProtocolTiming::new("A", vec![1], 1)]
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
    fn steady_state_d1_long_pre() {
        let inputs = vec![
            ProtocolTiming::new("A", vec![2], 1),
            ProtocolTiming::new("S", vec![2], 1),
        ];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_add_d1_long_pre", &to_dot(&graph))
    }

    #[test]
    fn steady_state_d1_unbounded_pre() {
        let inputs = vec![
            ProtocolTiming::unbounded("A", 1),
            ProtocolTiming::unbounded("S", 1),
        ];
        let graph = steady_driver_meta(inputs);

        snap("steady_state_add_d1_unbounded_pre", &to_dot(&graph))
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
    fn bounded_add_d1() {
        let graph = bounded_driver_meta(add_depth_one(), 2);
        snap("bounded_add_d1", &to_dot(&graph))
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
    fn unbounded_pre_phase_steady_state_simple() {
        // struct device {
        //     in a
        //     in b
        //     out ready
        //     out aout
        //     out bout
        // }
        // prot a(a) {
        //   DUT.a := a;
        //   step(); DUT.a := X; fork();
        //   step(); assert_eq(DUT.aout, a); step();
        // }

        // prot b(b) {
        //   while !DUT.ready() { step(); }
        //   step(); DUT.b := b;
        //   step(); assert_eq(DUT.s, b); step();
        // }
        let graph = steady_driver_meta(vec![
            ProtocolTiming::new("id", vec![1], 2),
            ProtocolTiming::unbounded("w", 0),
        ]);

        snap("unbounded_pre_phase_steady_state_simple", &to_dot(&graph))
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
        assert!(graph.nodes.iter().all(|node| node.state.post_phase.is_empty()));
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
