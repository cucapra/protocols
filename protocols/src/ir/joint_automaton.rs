use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::lowering::Lowerer;
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{
    Action, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation, remap_expr,
};

/// TODO: This should probbaly be standardized somewhere in the frontend
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

/// Annotate Transitions with a meta-type that is agnostic of how it is implemented
/// in the driver or the monitor version
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum JointTransitionKind {
    #[default]
    /// An edge not at a choice node; just continue as normal.
    Continue,
    /// At a choice node, launch Protocol `ProtocolId`
    Launch(ProtocolId),
    /// At a choice node, choose no Protocol and therefore flush all outstanding transactions.
    Stop,
}

/// The shared portion of the construction for joint drivers and monitors.
pub struct JointControlAutomaton {
    pub graph: ProtoGraph,
    pub choice_slots: FxHashMap<NodeId, Vec<usize>>,
    pub bank_counts: Vec<usize>,
    pub transition_kinds: FxHashMap<(NodeId, usize), JointTransitionKind>,
    pub instances: FxHashMap<NodeId, Vec<JointInstance>>,
}

#[derive(Clone)]
pub struct ProtocolShape {
    pub entry: NodeId,
    /// if there is a fork, the *unique* location of the forking node
    pub fork: Option<NodeId>,
    pub done: NodeId,
    /// the straight-line post-phase.
    pub post: Vec<NodeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A transaction that is in its post-phase.
struct PostTransaction {
    protocol: ProtocolId,
    /// where is it in its post-phase?
    post_index: usize,
    /// what transaction instance is this
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

pub fn analyze_shape(
    ctx: &Context,
    graph: &ProtoGraph,
    protocol: &Protocol,
) -> Result<ProtocolShape, JointAutomatonError> {
    let mut forks = Vec::new();
    let mut dones = Vec::new();
    for node in reachable_node_ids(ctx, graph, graph.entry) {
        for action in &graph[node].actions {
            match graph[action.op] {
                Op::Fork => {
                    if action.guard != ctx.get_true() {
                        return Err(unsupported(
                            protocol,
                            "the fork must be unconditional in its node",
                        ));
                    }
                    if !forks.contains(&node) {
                        forks.push(node);
                    }
                }
                Op::Done if !dones.contains(&node) => dones.push(node),
                _ => {}
            }
        }
    }
    if forks.len() > 1 {
        return Err(unsupported(protocol, "more than one reachable fork node"));
    }
    if dones.len() != 1 {
        return Err(unsupported(
            protocol,
            format!("expected one reachable done node, found {}", dones.len()),
        ));
    }
    let done = dones[0];
    let fork = forks.first().copied();
    let mut post = Vec::new();
    if let Some(fork) = fork {
        let mut current = fork;
        let mut seen = FxHashSet::default();
        while current != done {
            if !seen.insert(current) {
                return Err(unsupported(protocol, "the post-phase contains a cycle"));
            }
            post.push(current);
            let transitions = &graph[current].transitions;
            if transitions.len() != 1 {
                return Err(unsupported(protocol, "the post-phase is not straight-line"));
            }
            current = transitions[0].target;
        }
        if post.is_empty() {
            return Err(unsupported(
                protocol,
                "an explicit fork must be followed by at least one cycle",
            ));
        }
    }
    Ok(ProtocolShape {
        entry: graph.entry,
        fork,
        done,
        post,
    })
}

// arguments need to be renamed for the specific transaction instance to
// prevent collisions between concurrently running protocols
pub fn joint_argument_substitutions(
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

/// The number of live instances of `protocol` in `state`
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
        .sort_unstable_by_key(|post| (post.protocol, post.slot, post.post_index));
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
        let source = shape.post[transaction.post_index];
        let step = sources[transaction.protocol][source]
            .transitions
            .first()
            .expect("validated post node must have one transition");
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
        if transaction.post_index + 1 == shape.post.len() {
            debug_assert_eq!(step.target, shape.done);
            retired[transaction.protocol].push(transaction.slot);
        } else {
            posts.push(PostTransaction {
                post_index: transaction.post_index + 1,
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
    let frontier = if Some(target) == shape.fork {
        posts.push(PostTransaction {
            protocol,
            post_index: 0,
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

/// build a joint control automaton, agnostic to whether it's a driver or a monitor
/// the nodes themselves don't have any actions in them, except we insert `Done` actions
/// in Choice nodes where there are no outstanding transactions.
/// the transitions are not guarded by the driver selector or monitor liveness conditions;
/// these are added in the driver and monitor-specific constructions.
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
                control: shapes[transaction.protocol].post[transaction.post_index],
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
    for state in &states {
        for (protocol, count) in bank_counts.iter_mut().enumerate() {
            let live = live_count(state, protocol);
            let needed = live + usize::from(state.frontier == Frontier::Choice);
            *count = (*count).max(needed);
        }
        if state.frontier == Frontier::Choice {
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
        bank_counts,
        instances,
        transition_kinds,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::joint_driver::{JointDriverAutomaton, build_joint_driver_automaton};

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
            .iter()
            .filter(|protocol| selected.contains(&protocol.name.as_str()))
            .cloned()
            .collect();
        let driver = build_joint_driver_automaton(&mut ctx, &module, protocols, &symbols).unwrap();
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
    fn joint_choice_has_guarded_done_for_empty_stop() {
        let (driver, _, ctx) = build_selected("../tests/adders/adder_d1/add_d1.prot", &["add"]);
        let entry = driver.graph.entry;
        assert!(driver.graph[entry].actions.iter().any(|action| {
            matches!(driver.graph[action.op], Op::Done) && action.guard != ctx.get_true()
        }));
    }
}
