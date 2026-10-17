use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::lowering::Lowerer;
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{
    Action, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation, remap_expr
};

pub type ProtocolId = usize;

#[derive(Debug, Error)]
pub enum JointAutomatonError {
    #[error("a joint automaton needs at least one protocol")]
    EmptyProtocolSet,
    #[error("unsupported joint protocol {protocol}: {reason}")]
    UnsupportedProtocol { protocol: String, reason: String },
}

pub use JointAutomatonError as JointDriverError;

/// One transaction contributing actions to a joint control node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JointInstance {
    pub protocol: ProtocolId,
    pub slot: usize,
    /// Node in this protocol's prepared graph.
    pub control: NodeId,
    /// This cycle starts a fresh transaction in the slot.
    pub starts: bool,
}

/// Meaning of an edge before driver or monitor selection guards are attached.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum JointTransitionKind {
    #[default]
    Continue,
    Launch(ProtocolId),
    Stop,
}

/// Shared launch, pre-phase, post-phase, and draining control. Both driver and
/// monitor construction use this schedule and its FIFO slot rotations.
pub struct JointControlAutomaton {
    pub graph: ProtoGraph,
    pub choice_slots: FxHashMap<NodeId, Vec<usize>>,
    /// A sampled condition can delay a fork and its next launch within a node.
    pub choice_guards: FxHashMap<NodeId, ExprRef>,
    pub bank_counts: Vec<usize>,
    pub transition_kinds: FxHashMap<(NodeId, usize), JointTransitionKind>,
    pub instances: FxHashMap<NodeId, Vec<JointInstance>>,
}

/// An unbounded driver graph
pub struct JointDriverAutomaton {
    pub graph: ProtoGraph,
    pub protocols: Vec<Protocol>,
    pub transaction_valid: ExprRef,
    pub protocol_choice: ExprRef,
    /// At each choice node, the logical tail slot for every protocol.
    pub choice_slots: FxHashMap<NodeId, Vec<usize>>,
    /// A sampled condition can delay a fork and its next launch within a node.
    pub choice_guards: FxHashMap<NodeId, ExprRef>,
    pub bank_counts: Vec<usize>,
}

#[derive(Clone)]
struct ProtocolShape {
    entry: NodeId,
    forks: FxHashSet<NodeId>,
    conditional_forks: FxHashMap<NodeId, ExprRef>,
    done: NodeId,
    post: FxHashMap<NodeId, Transition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PostTransaction {
    protocol: ProtocolId,
    control: NodeId,
    slot: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Frontier {
    /// a new transaction starts this cycle
    Choice,
    /// a transaction is in the pre-phase (by our invariants,
    /// there is only ever one protocol in the `Pre` phase
    Pre {
        protocol: ProtocolId,
        control: NodeId,
        slot: usize,
    },
    /// No more forks. we're just draining whatever transactions are still live.
    Draining,
}

// TODO: This might end up getting turning into `MetaState`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct JointState {
    posts: Vec<PostTransaction>,
    frontier: Frontier,
}

fn unsupported(protocol: &Protocol, reason: impl Into<String>) -> JointAutomatonError {
    JointAutomatonError::UnsupportedProtocol {
        protocol: protocol.name.clone(),
        reason: reason.into(),
    }
}

fn analyze_shape(
    ctx: &mut Context,
    graph: &ProtoGraph,
    protocol: &Protocol,
) -> Result<ProtocolShape, JointAutomatonError> {
    let mut forks = FxHashMap::default();
    let mut dones = Vec::new();
    for node in reachable_node_ids(ctx, graph, graph.entry) {
        for action in &graph[node].actions {
            match graph[action.op] {
                Op::Fork => {
                    let prior = *forks.entry(node).or_insert(ctx.get_false());
                    forks.insert(node, ctx.or(prior, action.guard));
                }
                Op::Done if !dones.contains(&node) => dones.push(node),
                _ => {}
            }
        }
    }
    if dones.len() != 1 {
        return Err(unsupported(
            protocol,
            format!("expected one reachable done node, found {}", dones.len()),
        ));
    }
    let done = dones[0];
    let mut post = FxHashMap::default();
    let mut simplifier = patronus::expr::Simplifier::new(patronus::expr::SparseExprMap::default());
    let mut common_tail: Option<(NodeId, usize)> = None;
    let mut fork_nodes = forks.keys().copied().collect::<Vec<_>>();
    fork_nodes.sort_unstable();
    // Contraction can put the same fork in several nodes, guarded by the
    // condition that ends a wait. Only follow edges on which that fork executes.
    for fork in fork_nodes {
        let fork_guard = forks[&fork];
        let mut current = fork;
        let mut seen = FxHashSet::default();
        let mut tail_steps = 0;
        while current != done {
            if !seen.insert(current) {
                return Err(unsupported(protocol, "the post-phase contains a cycle"));
            }
            if current != fork && forks.contains_key(&current) {
                return Err(unsupported(protocol, "a post-phase reaches another fork"));
            }
            let guard = if current == fork {
                fork_guard
            } else {
                ctx.get_true()
            };
            let steps = graph[current]
                .transitions
                .iter()
                .filter(|edge| {
                    let enabled = ctx.and(guard, edge.guard);
                    simplifier.simplify(ctx, enabled) != ctx.get_false()
                })
                .collect::<Vec<_>>();
            if steps.len() != 1 {
                return Err(unsupported(protocol, "the post-phase is not straight-line"));
            }
            tail_steps += usize::from(steps[0].consumes_step);
            post.insert(current, steps[0].clone());
            current = steps[0].target;
        }
        // Equal durations preserve fork order at retirement, which lets both
        // drivers and monitors release their circular bank slots in FIFO order.
        if let Some((previous_fork, previous_steps)) = common_tail {
            if tail_steps != previous_steps {
                return Err(unsupported(
                    protocol,
                    format!(
                        "fork tails must have equal lengths for FIFO retirement: found {previous_steps} and {tail_steps} cycles at {previous_fork} and {fork}"
                    ),
                ));
            }
        } else {
            common_tail = Some((fork, tail_steps));
        }
    }
    let conditional_forks = forks
        .iter()
        .filter_map(|(&node, &guard)| (guard != ctx.get_true()).then_some((node, guard)))
        .collect();
    let forks = forks
        .into_iter()
        .filter_map(|(node, guard)| (guard == ctx.get_true()).then_some(node))
        .collect();
    Ok(ProtocolShape {
        entry: graph.entry,
        forks,
        conditional_forks,
        done,
        post,
    })
}

fn choice_guard(ctx: &Context, state: &JointState, shapes: &[ProtocolShape]) -> ExprRef {
    match state.frontier {
        Frontier::Choice => ctx.get_true(),
        Frontier::Pre {
            protocol, control, ..
        } => shapes[protocol]
            .conditional_forks
            .get(&control)
            .copied()
            .unwrap_or(ctx.get_false()),
        Frontier::Draining => ctx.get_false(),
    }
}

fn intern_state(
    graph: &mut ProtoGraph,
    states: &mut Vec<JointState>,
    ids: &mut FxHashMap<JointState, NodeId>,
    successor: JointState,
) -> NodeId {
    if let Some(&node) = ids.get(&successor) {
        return node;
    }
    let node = graph.n(Node::empty());
    ids.insert(successor.clone(), node);
    states.push(successor);
    node
}

// build the guard that selects one protocol at a launch point.
fn selector_guard(
    ctx: &mut Context,
    choice: ExprRef,
    protocol: ProtocolId,
    protocol_count: usize,
) -> ExprRef {
    if protocol_count == 1 {
        ctx.get_true()
    } else {
        let width = choice.get_bv_type(ctx).unwrap();
        let value = ctx.bit_vec_val(protocol, width);
        ctx.equal(choice, value)
    }
}

// arguments need to be renamed for the specific transaction instance to
// prevent collisions between concurrently running protocols
fn joint_argument_substitutions(
    ctx: &mut Context,
    graph: &ProtoGraph,
    protocol: &Protocol,
    symbols: &SymbolTable,
    slot: usize,
) -> FxHashMap<ExprRef, ExprRef> {
    // give this transaction's arguments names that cannot collide with other slots.
    protocol
        .args
        .iter()
        .filter_map(|arg| {
            let symbol = arg.symbol();
            let old = graph.symbol_expr(symbol)?;
            let width = old
                .get_bv_type(ctx)
                .expect("protocol arguments must be bit vectors");
            let name = symbols[symbol].name();
            let new = ctx.bv_symbol(&format!("joint.{name}#{slot}_{}", protocol.name), width);
            Some((old, new))
        })
        .collect()
}

fn live_count(state: &JointState, protocol: ProtocolId) -> usize {
    let posts = state
        .posts
        .iter()
        .filter(|transaction| transaction.protocol == protocol)
        .count();
    posts
        + usize::from(matches!(
            state.frontier,
            Frontier::Pre {
                protocol: active,
                ..
            } if active == protocol
        ))
}

// remove retired slots and return the slot shifts for each protocol.
fn normalize_successor(
    mut state: JointState,
    mut retired: Vec<Vec<usize>>,
    protocol_count: usize,
) -> (JointState, Vec<usize>) {
    // verify that each protocol retires its slots in order.
    let mut rotations = vec![0; protocol_count];
    for protocol in 0..protocol_count {
        retired[protocol].sort_unstable();
        retired[protocol].dedup();
        for (expected, slot) in retired[protocol].iter().copied().enumerate() {
            assert_eq!(slot, expected, "same-protocol retirement must be FIFO");
        }
        rotations[protocol] = retired[protocol].len();
    }

    // shift surviving slots down after retired slots are removed.
    for post in &mut state.posts {
        post.slot = post
            .slot
            .checked_sub(rotations[post.protocol])
            .expect("a surviving post transaction cannot precede a retired transaction");
    }
    if let Frontier::Pre { protocol, slot, .. } = &mut state.frontier {
        *slot = slot
            .checked_sub(rotations[*protocol])
            .expect("the active pre transaction cannot precede a retired transaction");
    }
    state
        .posts
        .sort_unstable_by_key(|post| (post.protocol, post.slot, post.control));
    (state, rotations)
}

// add one possible step, along with any slot shifts caused by retirement.
fn add_transition(
    ctx: &Context,
    graph: &mut ProtoGraph,
    source: NodeId,
    guard: ExprRef,
    target: NodeId,
    rotations: &[usize],
    protocols: &[Protocol],
) -> Option<usize> {
    if guard == ctx.get_false() {
        return None;
    }
    let mut transition = Transition::new(guard, target, true);
    transition.rotations = rotations
        .iter()
        .enumerate()
        .filter(|(_, amount)| **amount != 0)
        .map(|(protocol, &amount)| TransitionRotation {
            protocol: protocols[protocol].name.clone(),
            amount,
        })
        .collect();
    let index = graph[source].transitions.len();
    graph.push_transition(source, transition);
    Some(index)
}

struct AdvancedPosts {
    posts: Vec<PostTransaction>,
    guard: ExprRef,
    retired: Vec<Vec<usize>>,
}

fn advance_posts(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    sources: &[ProtoGraph],
    state: &JointState,
    shapes: &[ProtocolShape],
    protocols: &[Protocol],
    symbols: &SymbolTable,
) -> AdvancedPosts {
    // advance every post-phase transaction and combine its guards.
    let mut guard = ctx.get_true();
    let mut posts = Vec::new();
    let mut retired = vec![Vec::new(); protocols.len()];
    for transaction in &state.posts {
        let shape = &shapes[transaction.protocol];
        let step = &shape.post[&transaction.control];
        let substitutions = joint_argument_substitutions(
            ctx,
            &sources[transaction.protocol],
            &protocols[transaction.protocol],
            symbols,
            transaction.slot,
        );
        let step_guard = remap_expr(ctx, step.guard, &substitutions);
        guard = graph.and_guard(ctx, guard, step_guard);
        // mark the transaction for retirement when its last post cycle finishes.
        if step.target == shape.done {
            retired[transaction.protocol].push(transaction.slot);
        } else {
            posts.push(PostTransaction {
                control: step.target,
                ..*transaction
            });
        }
    }
    AdvancedPosts {
        posts,
        guard,
        retired,
    }
}

// update the front of a transaction after it takes one step.
fn successor_after_frontier_step(
    shapes: &[ProtocolShape],
    protocol: ProtocolId,
    slot: usize,
    target: NodeId,
    mut posts: Vec<PostTransaction>,
    mut retired: Vec<Vec<usize>>,
) -> (JointState, Vec<Vec<usize>>) {
    // decide whether the next frontier is another pre cycle, a choice, or retirement.
    let shape = &shapes[protocol];
    let frontier = if shape.forks.contains(&target) {
        posts.push(PostTransaction {
            protocol,
            control: target,
            slot,
        });
        Frontier::Choice
    } else if target == shape.done {
        retired[protocol].push(slot);
        Frontier::Choice
    } else {
        Frontier::Pre {
            protocol,
            control: target,
            slot,
        }
    };
    (JointState { posts, frontier }, retired)
}

/// Prepare each source once, before either driver or monitor composition.
pub fn prepare_joint_protocols(
    ctx: &mut Context,
    protocols: &[Protocol],
    symbols: &SymbolTable,
) -> Result<Vec<ProtoGraph>, JointAutomatonError> {
    if protocols.is_empty() {
        return Err(JointAutomatonError::EmptyProtocolSet);
    }
    Ok(protocols
        .iter()
        .map(|protocol| {
            let mut lowerer = Lowerer::new(protocol.ctx.clone(), symbols);
            let fragment = lowerer.lower_protocol_fragment(ctx, protocol, true, false);
            lowerer.postprocess_trace_fragment(ctx, &fragment);
            lowerer.ir.entry = fragment.entry;
            lowerer.ir.garbage_collect_unreachable(ctx);
            lowerer.ir
        })
        .collect())
}

/// Construct control independently of whether actions drive or observe pins.
/// Sources must be contracted, assignment-propagated single-protocol graphs.
/// Each fork must have a finite, straight-line tail to Done, and all tails
/// within one protocol must consume the same number of samples.
pub fn build_joint_control_automaton(
    ctx: &mut Context,
    protocols: &[Protocol],
    sources: &[ProtoGraph],
    symbols: &SymbolTable,
) -> Result<JointControlAutomaton, JointAutomatonError> {
    if protocols.is_empty() {
        return Err(JointAutomatonError::EmptyProtocolSet);
    }
    assert_eq!(protocols.len(), sources.len());
    let shapes = protocols
        .iter()
        .zip(sources)
        .map(|(protocol, graph)| analyze_shape(ctx, graph, protocol))
        .collect::<Result<Vec<_>, _>>()?;
    let mut graph = ProtoGraph::new(protocols[0].ctx.clone());
    for source in sources {
        graph.symbol_expr.extend(
            source
                .symbol_expr
                .iter()
                .map(|(&symbol, &expr)| (symbol, expr)),
        );
        graph.dont_cares.extend(source.dont_cares.iter().copied());
    }
    let mut instances = FxHashMap::default();

    let mut transition_kinds = FxHashMap::default();

    // Start at a choice between the protocols' first cycles.
    let entry_state = JointState {
        posts: Vec::new(),
        frontier: Frontier::Choice,
    };

    // discovered joint states; the cursor below uses this as the expansion worklist.
    let mut states = vec![entry_state.clone()];
    // canonical graph node for each discovered state, used to merge duplicates.
    let mut state_ids = FxHashMap::default();
    let entry = graph.n(Node::empty());
    state_ids.insert(entry_state, entry);
    let mut cursor = 0;

    // expand meta states until every reachable combination has been visited.
    while cursor < states.len() {
        let state = states[cursor].clone();
        let node = state_ids[&state];
        let mut active = Vec::new();
        for transaction in &state.posts {
            active.push(JointInstance {
                protocol: transaction.protocol,
                slot: transaction.slot,
                control: transaction.control,
                starts: false,
            });
        }
        match state.frontier {
            Frontier::Pre {
                protocol,
                control,
                slot,
            } => active.push(JointInstance {
                protocol,
                control,
                slot,
                starts: false,
            }),
            Frontier::Choice => {
                for (protocol, shape) in shapes.iter().enumerate() {
                    active.push(JointInstance {
                        protocol,
                        slot: live_count(&state, protocol),
                        control: shape.entry,
                        starts: true,
                    });
                }
            }
            Frontier::Draining => {}
        }
        let launch_guard = choice_guard(ctx, &state, &shapes);
        if state.frontier != Frontier::Choice && launch_guard != ctx.get_false() {
            for (protocol, shape) in shapes.iter().enumerate() {
                active.push(JointInstance {
                    protocol,
                    slot: live_count(&state, protocol),
                    control: shape.entry,
                    starts: true,
                });
            }
        }
        instances.insert(node, active);

        // compute the common post-phase step used by every outgoing transition.
        let advanced = advance_posts(
            ctx, &mut graph, sources, &state, &shapes, protocols, symbols,
        );
        match state.frontier {
            Frontier::Choice => {
                // Stop launching and drain the remaining transactions.
                if state.posts.is_empty() {
                    let done = graph.o(Op::Done);
                    graph.push_action(node, Action::new(ctx.get_true(), done));
                } else {
                    let successor = JointState {
                        posts: advanced.posts.clone(),
                        frontier: Frontier::Draining,
                    };
                    let (successor, rotations) =
                        normalize_successor(successor, advanced.retired.clone(), protocols.len());
                    let target = if let Some(&target) = state_ids.get(&successor) {
                        target
                    } else {
                        let target = graph.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    if let Some(index) = add_transition(
                        ctx,
                        &mut graph,
                        node,
                        advanced.guard,
                        target,
                        &rotations,
                        protocols,
                    ) {
                        transition_kinds.insert((node, index), JointTransitionKind::Stop);
                    }
                }

                // add one guarded transition for each possible protocol launch.
                for protocol in 0..protocols.len() {
                    let slot = live_count(&state, protocol);
                    let substitutions = joint_argument_substitutions(
                        ctx,
                        &sources[protocol],
                        &protocols[protocol],
                        symbols,
                        slot,
                    );
                    let source = shapes[protocol].entry;
                    for step in sources[protocol][source].transitions.clone() {
                        let step_guard = remap_expr(ctx, step.guard, &substitutions);
                        let guard = graph.and_guard(ctx, advanced.guard, step_guard);
                        let (successor, retired) = successor_after_frontier_step(
                            &shapes,
                            protocol,
                            slot,
                            step.target,
                            advanced.posts.clone(),
                            advanced.retired.clone(),
                        );
                        let (successor, rotations) =
                            normalize_successor(successor, retired, protocols.len());
                        let target = if let Some(&target) = state_ids.get(&successor) {
                            target
                        } else {
                            let target = graph.n(Node::empty());
                            state_ids.insert(successor.clone(), target);
                            states.push(successor);
                            target
                        };
                        if let Some(index) = add_transition(
                            ctx, &mut graph, node, guard, target, &rotations, protocols,
                        ) {
                            transition_kinds
                                .insert((node, index), JointTransitionKind::Launch(protocol));
                        }
                    }
                }
            }
            Frontier::Pre {
                protocol,
                control,
                slot,
            } => {
                // follow the active protocol's pre-phase control flow.
                let substitutions = joint_argument_substitutions(
                    ctx,
                    &sources[protocol],
                    &protocols[protocol],
                    symbols,
                    slot,
                );
                for step in sources[protocol][control].transitions.clone() {
                    let step_guard = remap_expr(ctx, step.guard, &substitutions);
                    let guard = graph.and_guard(ctx, advanced.guard, step_guard);
                    if launch_guard != ctx.get_false() {
                        let fork_guard = graph.and_guard(ctx, guard, launch_guard);
                        let mut posts = advanced.posts.clone();
                        let mut retired = advanced.retired.clone();
                        if step.target == shapes[protocol].done {
                            retired[protocol].push(slot);
                        } else {
                            posts.push(PostTransaction {
                                protocol,
                                control: step.target,
                                slot,
                            });
                        }
                        if fork_guard != ctx.get_false() {
                            let draining = JointState {
                                posts: posts.clone(),
                                frontier: Frontier::Draining,
                            };
                            let (draining, rotations) =
                                normalize_successor(draining, retired.clone(), protocols.len());
                            let target =
                                intern_state(&mut graph, &mut states, &mut state_ids, draining);
                            if let Some(index) = add_transition(
                                ctx, &mut graph, node, fork_guard, target, &rotations, protocols,
                            ) {
                                transition_kinds.insert((node, index), JointTransitionKind::Stop);
                            }
                            for fresh in 0..protocols.len() {
                                let fresh_slot = live_count(&state, fresh);
                                let substitutions = joint_argument_substitutions(
                                    ctx,
                                    &sources[fresh],
                                    &protocols[fresh],
                                    symbols,
                                    fresh_slot,
                                );
                                for first in &sources[fresh][shapes[fresh].entry].transitions {
                                    let first_guard = remap_expr(ctx, first.guard, &substitutions);
                                    let enabled = graph.and_guard(ctx, fork_guard, first_guard);
                                    if enabled == ctx.get_false() {
                                        continue;
                                    }
                                    let (successor, retired) = successor_after_frontier_step(
                                        &shapes,
                                        fresh,
                                        fresh_slot,
                                        first.target,
                                        posts.clone(),
                                        retired.clone(),
                                    );
                                    let (successor, rotations) =
                                        normalize_successor(successor, retired, protocols.len());
                                    let target = intern_state(
                                        &mut graph,
                                        &mut states,
                                        &mut state_ids,
                                        successor,
                                    );
                                    if let Some(index) = add_transition(
                                        ctx, &mut graph, node, enabled, target, &rotations,
                                        protocols,
                                    ) {
                                        transition_kinds.insert(
                                            (node, index),
                                            JointTransitionKind::Launch(fresh),
                                        );
                                    }
                                }
                            }
                        }
                    }
                    let waiting = graph.not_guard(ctx, launch_guard);
                    let guard = graph.and_guard(ctx, guard, waiting);
                    if guard == ctx.get_false() {
                        continue;
                    }
                    let (successor, retired) = successor_after_frontier_step(
                        &shapes,
                        protocol,
                        slot,
                        step.target,
                        advanced.posts.clone(),
                        advanced.retired.clone(),
                    );
                    let (successor, rotations) =
                        normalize_successor(successor, retired, protocols.len());
                    let target = if let Some(&target) = state_ids.get(&successor) {
                        target
                    } else {
                        let target = graph.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    let _ =
                        add_transition(ctx, &mut graph, node, guard, target, &rotations, protocols);
                }
            }
            Frontier::Draining => {
                // after the final launch, keep stepping until all posts retire.
                if state.posts.is_empty() {
                    let done = graph.o(Op::Done);
                    graph.push_action(node, Action::new(ctx.get_true(), done));
                } else {
                    let successor = JointState {
                        posts: advanced.posts,
                        frontier: Frontier::Draining,
                    };
                    let (successor, rotations) =
                        normalize_successor(successor, advanced.retired, protocols.len());
                    let target = if let Some(&target) = state_ids.get(&successor) {
                        target
                    } else {
                        let target = graph.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    let _ = add_transition(
                        ctx,
                        &mut graph,
                        node,
                        advanced.guard,
                        target,
                        &rotations,
                        protocols,
                    );
                }
            }
        }
        cursor += 1;
    }

    // compute how many slots each protocol needs in any reachable state.
    let mut bank_counts = vec![1; protocols.len()];
    let mut choice_slots = FxHashMap::default();
    let mut choice_guards = FxHashMap::default();
    for state in &states {
        let launch_guard = choice_guard(ctx, state, &shapes);
        for (protocol, count) in bank_counts.iter_mut().enumerate() {
            let live = live_count(state, protocol);
            let needed = live + usize::from(launch_guard != ctx.get_false());
            *count = (*count).max(needed);
        }
        if launch_guard != ctx.get_false() {
            choice_guards.insert(state_ids[state], launch_guard);
            let slots = (0..protocols.len())
                .map(|protocol| live_count(state, protocol))
                .collect();
            choice_slots.insert(state_ids[state], slots);
        }
    }

    // remove unreachable nodes and update choice-node metadata after compaction.
    graph.entry = entry;
    let node_map = graph.garbage_collect_unreachable(ctx);
    graph.simplify_all_exprs(ctx);
    let choice_slots = choice_slots
        .into_iter()
        .filter_map(|(node, slots)| Some((*node_map.get(&node)?, slots)))
        .collect();

    let choice_guards = choice_guards
        .into_iter()
        .filter_map(|(node, guard)| Some((*node_map.get(&node)?, guard)))
        .collect();

    let instances = instances
        .into_iter()
        .filter_map(|(node, active)| Some((*node_map.get(&node)?, active)))
        .collect();
    let mut transition_kinds = transition_kinds
        .into_iter()
        .filter_map(|((node, index), kind)| Some(((*node_map.get(&node)?, index), kind)))
        .collect::<FxHashMap<_, _>>();
    for (node, data) in graph.nodes() {
        for index in 0..data.transitions.len() {
            transition_kinds.entry((node, index)).or_default();
        }
    }
    Ok(JointControlAutomaton {
        graph,
        choice_slots,
        choice_guards,
        bank_counts,
        instances,
        transition_kinds,
    })
}

/// Construct one finite automaton that can drive an unbounded, back-to-back
/// sequence of the supplied protocols.
pub fn build_joint_driver_automaton(
    ctx: &mut Context,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
) -> Result<JointDriverAutomaton, JointDriverError> {
    let sources = prepare_joint_protocols(ctx, &protocols, symbols)?;
    let control = build_joint_control_automaton(ctx, &protocols, &sources, symbols)?;
    // create the shared inputs used to start the next transaction.
    let choice_width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    let transaction_valid = ctx.bv_symbol("transaction_valid", 1);
    let protocol_choice = ctx.bv_symbol("protocol_choice", choice_width);

    let launches = (0..protocols.len())
        .map(|protocol| {
            let selected = selector_guard(ctx, protocol_choice, protocol, protocols.len());
            ctx.and(transaction_valid, selected)
        })
        .collect::<Vec<_>>();
    let stop = ctx.not(transaction_valid);
    let mut lowerer = Lowerer::new(protocols[0].ctx.clone(), symbols);
    lowerer.ir = control.graph;
    // Different protocols have distinct symbols for the same DUT pins. Keep
    // assignment targets in the shared graph's DUT context, including draining
    // nodes where no new launch would otherwise supply that protocol's symbols.
    let inputs = lowerer.ir.dut_input_symbols(symbols).collect::<Vec<_>>();
    let targets = sources
        .iter()
        .flat_map(|source| source.dut_input_symbols(symbols))
        .map(|symbol| {
            let target = inputs
                .iter()
                .copied()
                .find(|&input| {
                    symbols[input].full_name(symbols) == symbols[symbol].full_name(symbols)
                })
                .expect("joint protocols must refer to the same DUT inputs");
            (symbol, target)
        })
        .collect::<FxHashMap<_, _>>();
    let nodes = lowerer.ir.nodes().map(|(id, _)| id).collect::<Vec<_>>();
    for node in nodes {
        for (index, edge) in lowerer.ir.node_mut(node).transitions.iter_mut().enumerate() {
            let selection = match control.transition_kinds[&(node, index)] {
                JointTransitionKind::Launch(protocol) => launches[protocol],
                JointTransitionKind::Stop => stop,
                JointTransitionKind::Continue => ctx.get_true(),
            };
            edge.guard = ctx.and(edge.guard, selection);
        }
        if control.choice_slots.contains_key(&node) {
            debug_assert!(
                lowerer.ir[node]
                    .actions
                    .iter()
                    .all(|action| matches!(lowerer.ir[action.op], Op::Done))
            );
            for action in lowerer.ir.node_mut(node).actions.iter_mut() {
                // The control builder emits only global Done actions here.
                action.guard = stop;
            }
        }
        lowerer.add_input_dont_care_assignments(ctx, &protocols[0], node);
        let mut choices = Vec::new();
        for instance in &control.instances[&node] {
            let source = &sources[instance.protocol];
            let substitutions = joint_argument_substitutions(
                ctx,
                source,
                &protocols[instance.protocol],
                symbols,
                instance.slot,
            );
            let mut actions = Vec::new();
            for action in &source[instance.control].actions {
                if matches!(source[action.op], Op::Fork | Op::Done) {
                    continue;
                }
                let op = source[action.op].remap(ctx, &substitutions, &targets);
                let op = lowerer.ir.o(op);
                let guard = remap_expr(ctx, action.guard, &substitutions);
                actions.push(Action::new(guard, op));
            }
            let copied = lowerer.ir.n(Node {
                actions,
                transitions: Vec::new(),
            });
            if instance.starts {
                let enabled = ctx.and(control.choice_guards[&node], launches[instance.protocol]);
                choices.push((copied, enabled));
            } else {
                lowerer.graft_contracted_entry(ctx, node, copied, ctx.get_true());
            }
        }
        if !choices.is_empty() {
            lowerer.graft_disjoint_contracted_entries(ctx, node, &choices);
        }
    }
    lowerer.ir.garbage_collect_unreachable(ctx);
    lowerer.ir.simplify_all_exprs(ctx);
    Ok(JointDriverAutomaton {
        graph: lowerer.ir,
        protocols,
        transaction_valid,
        protocol_choice,
        choice_slots: control.choice_slots,
        choice_guards: control.choice_guards,
        bank_counts: control.bank_counts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::graphviz::to_dot_string;

    fn build_selected(
        filename: &str,
        selected: &[&str],
    ) -> (JointDriverAutomaton, SymbolTable, Context) {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let mut ctx = Context::default();
        let protocols = module
            .protos
            .into_iter()
            .filter(|protocol| selected.contains(&protocol.name.as_str()))
            .collect();
        let driver = build_joint_driver_automaton(&mut ctx, protocols, &symbols).unwrap();
        (driver, symbols, ctx)
    }

    #[test]
    fn joint_d1_uses_two_banks_and_is_cyclic() {
        let (driver, _, _) = build_selected("../tests/adders/adder_d1/add_d1.prot", &["add"]);
        assert_eq!(driver.bank_counts, vec![2]);
        assert!(driver.graph.nodes().count() <= 5);
        assert!(
            driver
                .graph
                .nodes()
                .flat_map(|(_, node)| &node.transitions)
                .any(|transition| !transition.rotations.is_empty())
        );
    }

    #[test]
    fn joint_d2_uses_three_banks() {
        let (driver, _, _) = build_selected("../tests/adders/adder_d2/add_d2.prot", &["add"]);
        assert_eq!(driver.bank_counts, vec![3]);
        assert!(driver.graph.nodes().count() <= 8);
    }

    #[test]
    fn joint_unbounded_pre_control_is_finite() {
        let (driver, symbols, ctx) = build_selected(
            "../tests/meta/unbounded_pre_phase_steady_state_simple.prot",
            &["id", "w"],
        );
        assert!(driver.graph.nodes().count() <= 16);
        let dot = to_dot_string(&ctx, &driver.graph, &symbols);
        assert!(dot.contains("DUT.ready"));
        assert!(dot.contains("transaction_valid"));
    }

    #[test]
    fn joint_choice_has_guarded_done_for_empty_stop() {
        let (driver, _, ctx) = build_selected("../tests/adders/adder_d1/add_d1.prot", &["add"]);
        let entry = driver.graph.entry;
        assert!(driver.graph[entry].actions.iter().any(|action| {
            matches!(driver.graph[action.op], Op::Done) && action.guard != ctx.get_true()
        }));
    }
}
