use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{
    Action, Node, NodeId, Op, ProtoGraph, Transition, TransitionRotation,
};

pub type ProtocolId = usize;

#[derive(Debug, Error)]
pub enum JointDriverError {
    #[error("a joint driver needs at least one protocol")]
    EmptyProtocolSet,
    #[error("unsupported joint-driver protocol {protocol}: {reason}")]
    UnsupportedProtocol { protocol: String, reason: String },
}

/// An unbounded driver graph
pub struct JointDriverAutomaton {
    pub graph: ProtoGraph,
    pub protocols: Vec<Protocol>,
    pub transaction_valid: ExprRef,
    pub protocol_choice: ExprRef,
    /// At each choice node, the logical tail slot for every protocol.
    pub choice_slots: FxHashMap<NodeId, Vec<usize>>,
    pub bank_counts: Vec<usize>,
}

#[derive(Clone)]
pub struct ProtocolShape {
    pub fragment: LoweredFragmentInfo,
    pub fork: Option<NodeId>,
    pub done: NodeId,
    pub post: Vec<NodeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PostTransaction {
    protocol: ProtocolId,
    post_index: usize,
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

fn unsupported(protocol: &Protocol, reason: impl Into<String>) -> JointDriverError {
    JointDriverError::UnsupportedProtocol {
        protocol: protocol.name.clone(),
        reason: reason.into(),
    }
}

pub fn analyze_shape(
    ctx: &Context,
    graph: &ProtoGraph, // assumes the graph is contracted and unreachable edges are pruned
    protocol: &Protocol,
    fragment: LoweredFragmentInfo,
) -> Result<ProtocolShape, JointDriverError> {
    // find the fork and done nodes reachable from the protocol entry.
    let mut forks = Vec::new();
    let mut dones = Vec::new();
    for node in reachable_node_ids(ctx, graph, fragment.entry) {
        for action in &graph[node].actions {
            match graph[action.op] {
                Op::Fork if !forks.contains(&node) => forks.push(node),
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

    // check that the post-phase is a finite straight line.
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
        fragment,
        fork,
        done,
        post,
    })
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
fn instance_substitutions(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
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
) {
    if guard == ctx.get_false() {
        return;
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
    graph.push_transition(source, transition);
}

struct AdvancedPosts {
    posts: Vec<PostTransaction>,
    guard: ExprRef,
    retired: Vec<Vec<usize>>,
}

fn advance_posts(
    ctx: &mut Context,
    lowerer: &mut Lowerer<'_>,
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
        let step = lowerer.ir[source]
            .transitions
            .first()
            .cloned()
            .expect("validated post node must have one transition");
        let substitutions = instance_substitutions(
            ctx,
            &mut lowerer.ir,
            &protocols[transaction.protocol],
            symbols,
            transaction.slot,
        );
        let step_guard = lowerer.remap_expr(ctx, step.guard, &substitutions);
        guard = lowerer.ir.and_guard(ctx, guard, step_guard);
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

/// Construct one finite automaton that can drive an unbounded, back-to-back
/// sequence of the supplied protocols.
pub fn build_joint_driver_automaton(
    ctx: &mut Context,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
) -> Result<JointDriverAutomaton, JointDriverError> {
    // reject inputs that cannot be represented by one joint driver.
    if protocols.is_empty() {
        return Err(JointDriverError::EmptyProtocolSet);
    }
    // lower each protocol once and record the shape needed to combine it.
    let mut lowerer = Lowerer::new(protocols[0].ctx.clone(), symbols);
    let mut shapes = Vec::with_capacity(protocols.len());
    for protocol in &protocols {
        let fragment = lowerer.lower_protocol_fragment(ctx, protocol, true, false);
        lowerer.postprocess_trace_fragment(ctx, &fragment);
        shapes.push(analyze_shape(ctx, &lowerer.ir, protocol, fragment)?);
    }

    // create the shared inputs used to start the next transaction.
    let choice_width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    let transaction_valid = ctx.bv_symbol("transaction_valid", 1);
    let protocol_choice = ctx.bv_symbol("protocol_choice", choice_width);

    // start from a state where the driver can choose its first transaction.
    let entry_state = JointState {
        posts: Vec::new(),
        frontier: Frontier::Choice,
    };

    // discovered joint states; the cursor below uses this as the expansion worklist.
    let mut states = vec![entry_state.clone()];
    // canonical graph node for each discovered state, used to merge duplicates.
    let mut state_ids = FxHashMap::default();
    let entry = lowerer.ir.n(Node::empty());
    state_ids.insert(entry_state, entry);
    let mut cursor = 0;

    // expand meta states until every reachable combination has been visited.
    while cursor < states.len() {
        let state = states[cursor].clone();
        let node = state_ids[&state];
        lowerer.add_input_dont_care_assignments(ctx, &protocols[0], node);

        // copy the actions of all active post phases into this state.
        for transaction in &state.posts {
            let substitutions = instance_substitutions(
                ctx,
                &mut lowerer.ir,
                &protocols[transaction.protocol],
                symbols,
                transaction.slot,
            );
            let source = shapes[transaction.protocol].post[transaction.post_index];
            let actions = lowerer.copy_node_actions(ctx, source, &substitutions, false);
            lowerer.graft_contracted_entry(ctx, node, actions, ctx.get_true());
        }

        // copy the active pre phase or the next choice into this state.
        match state.frontier {
            Frontier::Pre {
                protocol,
                control,
                slot,
            } => {
                let substitutions = instance_substitutions(
                    ctx,
                    &mut lowerer.ir,
                    &protocols[protocol],
                    symbols,
                    slot,
                );
                let actions = lowerer.copy_node_actions(ctx, control, &substitutions, false);
                lowerer.graft_contracted_entry(ctx, node, actions, ctx.get_true());
            }
            Frontier::Choice => {
                let choices = protocols
                    .iter()
                    .enumerate()
                    .map(|(protocol, ast)| {
                        let slot = live_count(&state, protocol);
                        let substitutions =
                            instance_substitutions(ctx, &mut lowerer.ir, ast, symbols, slot);
                        let actions = lowerer.copy_node_actions(
                            ctx,
                            shapes[protocol].fragment.entry,
                            &substitutions,
                            false,
                        );
                        let selected =
                            selector_guard(ctx, protocol_choice, protocol, protocols.len());
                        let guard = lowerer.ir.and_guard(ctx, transaction_valid, selected);
                        (actions, guard)
                    })
                    .collect::<Vec<_>>();
                lowerer.graft_disjoint_contracted_entries(ctx, node, &choices);
            }
            Frontier::Draining => {}
        }

        // compute the common post-phase step used by every outgoing transition.
        let advanced = advance_posts(ctx, &mut lowerer, &state, &shapes, &protocols, symbols);
        match state.frontier {
            Frontier::Choice => {
                // allow the driver to stop when no transaction is being launched.
                let not_valid = lowerer.ir.not_guard(ctx, transaction_valid);
                if state.posts.is_empty() {
                    let done = lowerer.ir.o(Op::Done);
                    lowerer.ir.push_action(node, Action::new(not_valid, done));
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
                        let target = lowerer.ir.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    let guard = lowerer.ir.and_guard(ctx, advanced.guard, not_valid);
                    add_transition(
                        ctx,
                        &mut lowerer.ir,
                        node,
                        guard,
                        target,
                        &rotations,
                        &protocols,
                    );
                }

                // add one guarded transition for each possible protocol launch.
                for protocol in 0..protocols.len() {
                    let slot = live_count(&state, protocol);
                    let substitutions = instance_substitutions(
                        ctx,
                        &mut lowerer.ir,
                        &protocols[protocol],
                        symbols,
                        slot,
                    );
                    let selected = selector_guard(ctx, protocol_choice, protocol, protocols.len());
                    let launch = lowerer.ir.and_guard(ctx, transaction_valid, selected);
                    let source = shapes[protocol].fragment.entry;
                    for step in lowerer.ir[source].transitions.clone() {
                        let step_guard = lowerer.remap_expr(ctx, step.guard, &substitutions);
                        let guard = lowerer.ir.and_guard(ctx, advanced.guard, launch);
                        let guard = lowerer.ir.and_guard(ctx, guard, step_guard);
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
                            let target = lowerer.ir.n(Node::empty());
                            state_ids.insert(successor.clone(), target);
                            states.push(successor);
                            target
                        };
                        add_transition(
                            ctx,
                            &mut lowerer.ir,
                            node,
                            guard,
                            target,
                            &rotations,
                            &protocols,
                        );
                    }
                }
            }
            Frontier::Pre {
                protocol,
                control,
                slot,
            } => {
                // follow the active protocol's pre-phase control flow.
                let substitutions = instance_substitutions(
                    ctx,
                    &mut lowerer.ir,
                    &protocols[protocol],
                    symbols,
                    slot,
                );
                for step in lowerer.ir[control].transitions.clone() {
                    let step_guard = lowerer.remap_expr(ctx, step.guard, &substitutions);
                    let guard = lowerer.ir.and_guard(ctx, advanced.guard, step_guard);
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
                        let target = lowerer.ir.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    add_transition(
                        ctx,
                        &mut lowerer.ir,
                        node,
                        guard,
                        target,
                        &rotations,
                        &protocols,
                    );
                }
            }
            Frontier::Draining => {
                // after the final launch, keep stepping until all posts retire.
                if state.posts.is_empty() {
                    let done = lowerer.ir.o(Op::Done);
                    lowerer
                        .ir
                        .push_action(node, Action::new(ctx.get_true(), done));
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
                        let target = lowerer.ir.n(Node::empty());
                        state_ids.insert(successor.clone(), target);
                        states.push(successor);
                        target
                    };
                    add_transition(
                        ctx,
                        &mut lowerer.ir,
                        node,
                        advanced.guard,
                        target,
                        &rotations,
                        &protocols,
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
    lowerer.ir.entry = entry;
    let node_map = lowerer.ir.garbage_collect_unreachable(ctx);
    lowerer.ir.simplify_all_exprs(ctx);
    let choice_slots = choice_slots
        .into_iter()
        .filter_map(|(node, slots)| Some((*node_map.get(&node)?, slots)))
        .collect();

    Ok(JointDriverAutomaton {
        graph: lowerer.ir,
        protocols,
        transaction_valid,
        protocol_choice,
        choice_slots,
        bank_counts,
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
