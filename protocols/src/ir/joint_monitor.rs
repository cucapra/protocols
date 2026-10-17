//! Unbounded monitor composition using the driver's joint control schedule.
//!
//! At a choice node, every protocol tries its first cycle on the current sample.
//! The surviving candidate selects the edge. We assume there is at most one;
//! no uniqueness check or external launch/protocol selector is generated.
//! Each individual monitor's equality constraints become guarded updates that
//! clear its live flag before instances are composed. Existing transactions must
//! survive, and a choice must have a surviving candidate, or execution enters
//! the absorbing bad state. Assignments read the incoming state and are applied
//! together before edges read the updated live flags. This module does not
//! construct a transition system or substitute assignment expressions into edges.

use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::driver_to_monitor::{
    MonitorAutomaton, MonitorConversionError, convert_driver_to_monitor
};
use crate::ir::joint_automaton::{
    JointAutomatonError, JointControlAutomaton, JointTransitionKind, ProtocolId, build_joint_control_automaton, prepare_joint_protocols
};
use crate::ir::proto_graph::{Action, Assignment, Node, NodeId, Op, Transition, remap_expr};
use crate::ir::simplify_monitor::simplify_monitor;

/// Parameter ownership includes both the protocol and its logical FIFO slot.
pub type InstanceParameter = (ProtocolId, usize, SymbolId);
pub type InstanceId = (ProtocolId, usize);

/// A monitor using the driver's unbounded transaction schedule. Assignment
/// expressions read the incoming state; edges read the state after all node
/// assignments have been applied, before any edge's FIFO rotations.
pub struct JointMonitorAutomaton {
    pub control: JointControlAutomaton,
    /// Absorbing state for an ordinary trace mismatch, separate from internal errors.
    pub bad_state: NodeId,
    pub protocols: Vec<Protocol>,
    pub value_registers: FxHashMap<InstanceParameter, SymbolId>,
    pub knownness_registers: FxHashMap<InstanceParameter, SymbolId>,
    pub live_registers: FxHashMap<InstanceId, SymbolId>,
    pub register_inits: FxHashMap<SymbolId, ExprRef>,
    /// Logical full-width masks at node entry, including masks with no register.
    pub knownness_outputs: FxHashMap<NodeId, FxHashMap<InstanceParameter, ExprRef>>,
    /// (Node, action index) -> owning instance. Global Done actions have no owner.
    pub action_owners: FxHashMap<(NodeId, usize), InstanceId>,
}

impl JointMonitorAutomaton {
    pub fn to_dot_string(&self, ctx: &Context, symbols: &SymbolTable) -> String {
        crate::ir::graphviz::to_dot_string_with_node_labels(
            ctx,
            &self.control.graph,
            symbols,
            &[(self.bad_state, "BAD STATE")],
        )
    }
}

#[derive(Debug, Error)]
pub enum JointMonitorError {
    #[error(transparent)]
    Control(#[from] JointAutomatonError),
    #[error("cannot monitor protocol {protocol}: {source}")]
    Conversion {
        protocol: String,
        source: MonitorConversionError,
    },
}

/// Prepare and convert each protocol, explicitly simplify its monitor, then
/// compose instances with the same control construction used for driving.
pub fn build_joint_monitor_automaton(
    ctx: &mut Context,
    protocols: Vec<Protocol>,
    symbols: &mut SymbolTable,
) -> Result<JointMonitorAutomaton, JointMonitorError> {
    let sources = prepare_joint_protocols(ctx, &protocols, symbols)?;
    let mut monitors = Vec::new();
    for (protocol, source) in protocols.iter().zip(sources) {
        let monitor = convert_driver_to_monitor(ctx, source, symbols).map_err(|source| {
            JointMonitorError::Conversion {
                protocol: protocol.name.clone(),
                source,
            }
        })?;
        monitors.push(simplify_monitor(ctx, monitor, symbols));
    }
    compose_joint_monitor_automaton(ctx, protocols, monitors, symbols)
}

/// Compose already converted monitors. Callers may supply either naive or
/// simplified monitors; generated assignments never undergo driver propagation.
pub fn compose_joint_monitor_automaton(
    ctx: &mut Context,
    protocols: Vec<Protocol>,
    mut monitors: Vec<MonitorAutomaton>,
    symbols: &mut SymbolTable,
) -> Result<JointMonitorAutomaton, JointMonitorError> {
    for monitor in &mut monitors {
        lower_constraints(ctx, monitor);
    }
    let sources = monitors
        .iter()
        .map(|monitor| monitor.graph.clone())
        .collect::<Vec<_>>();
    let mut control = build_joint_control_automaton(ctx, &protocols, &sources, symbols)?;
    let bad_state = control.graph.n(Node::empty());
    control
        .graph
        .push_transition(bad_state, Transition::new(ctx.get_true(), bad_state, true));
    control.instances.insert(bad_state, Vec::new());
    control
        .transition_kinds
        .insert((bad_state, 0), JointTransitionKind::Continue);
    let mut result = JointMonitorAutomaton {
        control,
        bad_state,
        protocols,
        value_registers: FxHashMap::default(),
        knownness_registers: FxHashMap::default(),
        live_registers: FxHashMap::default(),
        register_inits: FxHashMap::default(),
        knownness_outputs: FxHashMap::default(),
        action_owners: FxHashMap::default(),
    };
    let mut instance_targets = FxHashMap::default();
    let mut instance_exprs = FxHashMap::default();
    for (protocol, monitor) in monitors.iter().enumerate() {
        for slot in 0..result.control.bank_counts[protocol] {
            let mut targets = FxHashMap::default();
            let mut substitutions = FxHashMap::default();
            // Stable ordering keeps generated names and DOT output reproducible.
            let mut registers = monitor.register_inits.keys().copied().collect::<Vec<_>>();
            registers.sort_unstable();
            for old in registers {
                let base = format!(
                    "{}#{}_{}",
                    symbols[old].name(),
                    slot,
                    result.protocols[protocol].name
                );
                let mut name = base.clone();
                let mut suffix = 1;
                while symbols.symbol_id_from_name_in_active_scope(&name).is_some() {
                    name = format!("{base}_{suffix}");
                    suffix += 1;
                }
                let register = symbols.add_without_parent(
                    name,
                    symbols[old].tpe(),
                    SymbolKind::AutomatonState,
                );
                let width = monitor
                    .graph
                    .symbol_expr(old)
                    .unwrap()
                    .get_bv_type(ctx)
                    .unwrap();
                let expr = ctx.bv_symbol(&symbols[register].full_name(symbols), width);
                result.control.graph.cache_symbol_expr(register, expr);
                targets.insert(old, register);
                substitutions.insert(monitor.graph.symbol_expr(old).unwrap(), expr);
                // No transaction is active initially. Launching restores the
                // template's live=true along with fresh parameter values/masks.
                let init = if old == monitor.live_register {
                    ctx.get_false()
                } else {
                    monitor.register_inits[&old]
                };
                result.register_inits.insert(register, init);
            }
            for (&argument, &register) in &monitor.value_registers {
                result
                    .value_registers
                    .insert((protocol, slot, argument), targets[&register]);
            }
            for (&argument, &register) in &monitor.knownness_registers {
                result
                    .knownness_registers
                    .insert((protocol, slot, argument), targets[&register]);
            }
            result
                .live_registers
                .insert((protocol, slot), targets[&monitor.live_register]);
            instance_targets.insert((protocol, slot), targets);
            instance_exprs.insert((protocol, slot), substitutions);
        }
    }
    let nodes = result
        .control
        .graph
        .nodes()
        .map(|(node, _)| node)
        .filter(|&node| node != bad_state)
        .collect::<Vec<_>>();
    result
        .knownness_outputs
        .insert(bad_state, FxHashMap::default());
    for node in nodes {
        let mut outputs = FxHashMap::default();
        let mut ongoing = ctx.get_true();
        let mut any_launch = ctx.get_false();
        let mut launches = FxHashMap::default();
        for instance in result.control.instances[&node].clone() {
            let owner = (instance.protocol, instance.slot);
            let monitor = &monitors[instance.protocol];
            let targets = &instance_targets[&owner];
            let live_register = result.live_registers[&owner];
            let live = result.control.graph.symbol_expr(live_register).unwrap();
            let activation = if instance.starts {
                result.control.choice_guards[&node]
            } else {
                ctx.get_true()
            };
            let mut substitutions = instance_exprs[&owner].clone();
            if instance.starts {
                // Every candidate starts fresh, including slots used before.
                // All first-cycle observations read these initial expressions.
                for (&register, &init) in &monitor.register_inits {
                    substitutions.insert(monitor.graph.symbol_expr(register).unwrap(), init);
                }
            }
            for (&argument, &expr) in &monitor.knownness_outputs[&instance.control] {
                let expr = remap_expr(ctx, expr, &substitutions);
                let zero = ctx.zero(expr.get_bv_type(ctx).unwrap());
                let expr = ctx.ite(activation, expr, zero);
                outputs.insert((instance.protocol, instance.slot, argument), expr);
            }
            let mut assigned = FxHashSet::default();
            for action in &monitor.graph[instance.control].actions {
                if matches!(monitor.graph[action.op], Op::Fork | Op::Done) {
                    continue;
                }
                let mut op = monitor.graph[action.op].remap(ctx, &substitutions, targets);
                let mut guard = remap_expr(ctx, action.guard, &substitutions);
                if let Op::Assign(register, assignment) = &mut op {
                    assert_eq!(
                        guard,
                        ctx.get_true(),
                        "monitor assignment guards must be true"
                    );
                    assigned.insert(*register);
                    for (guard, _) in &mut assignment.concretes {
                        *guard = ctx.and(activation, *guard);
                    }
                } else {
                    guard = ctx.and(activation, guard);
                }
                push_owned_action(&mut result, node, owner, guard, op);
            }
            if instance.starts {
                // Even an entry hold removed by simplification must reset its
                // register: this is a fresh attempt, not the previous occupant.
                let mut registers = monitor.register_inits.iter().collect::<Vec<_>>();
                registers.sort_unstable_by_key(|(register, _)| **register);
                for (&old, &init) in registers {
                    let register = targets[&old];
                    if old != monitor.live_register && !assigned.contains(&register) {
                        let assignment = Assignment::concrete(ctx.get_false(), activation, init);
                        push_owned_action(
                            &mut result,
                            node,
                            owner,
                            ctx.get_true(),
                            Op::Assign(register, assignment),
                        );
                    }
                }
            }
            // Edges execute after assignments, so they read this cycle's live
            // flag directly. Only instances scheduled here affect the guards.
            if instance.starts {
                any_launch = ctx.or(any_launch, live);
                launches.insert(instance.protocol, live);
            } else {
                ongoing = ctx.and(ongoing, live);
            }
        }
        let required = if let Some(&activation) = result.control.choice_guards.get(&node) {
            let waiting = ctx.not(activation);
            let choice_survives = ctx.or(waiting, any_launch);
            ctx.and(ongoing, choice_survives)
        } else {
            ongoing
        };
        for (index, edge) in result
            .control
            .graph
            .node_mut(node)
            .transitions
            .iter_mut()
            .enumerate()
        {
            let selected = match result.control.transition_kinds[&(node, index)] {
                JointTransitionKind::Launch(protocol) => launches[&protocol],
                JointTransitionKind::Stop => ctx.get_false(),
                JointTransitionKind::Continue => ctx.get_true(),
            };
            let survives = ctx.and(ongoing, selected);
            edge.guard = ctx.and(edge.guard, survives);
        }
        let failed = ctx.not(required);
        let index = result.control.graph[node].transitions.len();
        result
            .control
            .graph
            .push_transition(node, Transition::new(failed, bad_state, true));
        result
            .control
            .transition_kinds
            .insert((node, index), JointTransitionKind::Continue);
        // Done at a choice with no older transactions marks a valid waveform
        // boundary. Consuming another sample requires a surviving launch edge.
        result.knownness_outputs.insert(node, outputs);
    }
    result.control.graph.simplify_all_exprs(ctx);
    Ok(result)
}

/// Lower constraints in each individual monitor, before unbounded composition.
fn lower_constraints(ctx: &mut Context, monitor: &mut MonitorAutomaton) {
    let graph = &mut monitor.graph;
    let live = graph.symbol_expr(monitor.live_register).unwrap();
    let nodes = graph.nodes().map(|(node, _)| node).collect::<Vec<_>>();
    for node in nodes {
        let mut failed = ctx.get_false();
        let mut actions = Vec::new();
        for action in graph[node].actions.clone() {
            if let Op::AssertEq(lhs, rhs) = graph[action.op] {
                // [guard] assert_eq(lhs, rhs) becomes a reason to clear live:
                // guard && !(lhs == rhs).
                let equal = ctx.equal(lhs, rhs);
                let unequal = ctx.not(equal);
                let failure = ctx.and(action.guard, unequal);
                failed = ctx.or(failed, failure);
            } else {
                actions.push(action);
            }
        }
        let failed = graph.simplifier.simplify(ctx, failed);
        let mut concretes = Vec::new();
        if failed != ctx.get_false() {
            concretes.push((failed, ctx.get_false()));
        }
        // The kill alternative has priority; otherwise preserve liveness.
        // Fresh-instance copying substitutes live=true into this held value.
        concretes.push((ctx.get_true(), live));
        let op = graph.o(Op::Assign(
            monitor.live_register,
            Assignment {
                dont_care: ctx.get_false(),
                concretes,
            },
        ));
        actions.push(Action::new(ctx.get_true(), op));
        graph.node_mut(node).actions = actions;
    }
    let node_map = graph.garbage_collect_unreachable(ctx);
    monitor.knownness_outputs = std::mem::take(&mut monitor.knownness_outputs)
        .into_iter()
        .filter_map(|(node, outputs)| Some((*node_map.get(&node)?, outputs)))
        .collect();
}

fn push_owned_action(
    monitor: &mut JointMonitorAutomaton,
    node: NodeId,
    owner: InstanceId,
    guard: ExprRef,
    op: Op,
) {
    let graph = &mut monitor.control.graph;
    let index = graph[node].actions.len();
    let op = graph.o(op);
    graph.push_action(node, Action::new(guard, op));
    monitor.action_owners.insert((node, index), owner);
}

#[cfg(test)]
mod tests;
