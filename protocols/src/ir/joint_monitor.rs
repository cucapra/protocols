//! Unbounded monitor composition using the driver's joint control schedule.
//!
//! Launch choices describe a candidate interpretation of the samples. Constraints
//! remain ordinary AssertEq actions, owned by individual transaction instances.
//! This assumes protocol choice is unambiguous after the first cycle; it does
//! not construct sets of competing parameter environments or a transition system.

use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::driver_to_monitor::{
    MonitorAutomaton, MonitorConversionError, convert_driver_to_monitor
};
use crate::ir::joint_automaton::{
    JointAutomatonError, JointControlAutomaton, ProtocolId, build_joint_control_automaton, prepare_joint_protocols
};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, remap_expr};
use crate::ir::simplify_monitor::simplify_monitor;

/// Parameter ownership includes both the protocol and its logical FIFO slot.
pub type InstanceParameter = (ProtocolId, usize, SymbolId);
pub type InstanceId = (ProtocolId, usize);

pub struct JointMonitorAutomaton {
    pub control: JointControlAutomaton,
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
        crate::ir::graphviz::to_dot_string(ctx, &self.control.graph, symbols)
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
    monitors: Vec<MonitorAutomaton>,
    symbols: &mut SymbolTable,
) -> Result<JointMonitorAutomaton, JointMonitorError> {
    let sources = monitors
        .iter()
        .map(|monitor| monitor.graph.clone())
        .collect::<Vec<_>>();
    let control = build_joint_control_automaton(ctx, &protocols, &sources, symbols)?;
    let mut result = JointMonitorAutomaton {
        control,
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
        .collect::<Vec<_>>();
    for node in nodes {
        let mut outputs = FxHashMap::default();
        for instance in result.control.instances[&node].clone() {
            let owner = (instance.protocol, instance.slot);
            let monitor = &monitors[instance.protocol];
            let targets = &instance_targets[&owner];
            let mut substitutions = instance_exprs[&owner].clone();
            if instance.starts {
                // First-cycle checks and learning read fresh initial values,
                // even if this physical slot held an older transaction before.
                for (&register, &init) in &monitor.register_inits {
                    substitutions.insert(monitor.graph.symbol_expr(register).unwrap(), init);
                }
            }
            for (&argument, &expr) in &monitor.knownness_outputs[&instance.control] {
                let expr = remap_expr(ctx, expr, &substitutions);
                let zero = ctx.zero(expr.get_bv_type(ctx).unwrap());
                let expr = ctx.ite(instance.guard, expr, zero);
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
                    assignment.dont_care =
                        result
                            .control
                            .graph
                            .and_guard(ctx, instance.guard, assignment.dont_care);
                    for (g, _) in &mut assignment.concretes {
                        *g = result.control.graph.and_guard(ctx, instance.guard, *g);
                    }
                } else {
                    guard = result.control.graph.and_guard(ctx, instance.guard, guard);
                }
                push_owned_action(&mut result, node, owner, guard, op);
            }
            if instance.starts {
                // Optimization may have removed a hold at entry. Such a register
                // still needs resetting when its slot is reused.
                let mut registers = monitor.register_inits.iter().collect::<Vec<_>>();
                registers.sort_unstable_by_key(|(register, _)| **register);
                for (&old, &init) in registers {
                    let register = targets[&old];
                    if !assigned.contains(&register) {
                        let assignment =
                            Assignment::concrete(ctx.get_false(), instance.guard, init);
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
        }
        result.knownness_outputs.insert(node, outputs);
    }
    result.control.graph.simplify_all_exprs(ctx);
    Ok(result)
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
