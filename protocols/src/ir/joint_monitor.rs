use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::driver_to_monitor::{
    MonitorAutomaton, MonitorConversionError, convert_driver_to_monitor, opt_iter_count,
    simplify_monitor,
};
use crate::ir::joint_automaton::{
    JointAutomatonError, JointControlAutomaton, JointTransitionKind, ProtocolId,
    build_joint_control_automaton, prepare_joint_protocols,
};
use crate::ir::proto_graph::{Action, Assignment, Node, NodeId, Op, Transition, remap_expr};
use crate::ir::register_simplify::simplify_guarded;

/// Parameter ownership includes both the protocol and its logical FIFO slot.
pub type InstanceParameter = (ProtocolId, usize, SymbolId);
pub type InstanceId = (ProtocolId, usize);

pub struct JointMonitorAutomaton {
    pub control: JointControlAutomaton,
    /// Absorbing state for an ordinary trace mismatch, separate from internal errors.
    pub bad_state: NodeId,
    pub protocols: Vec<Protocol>,
    pub value_registers: FxHashMap<InstanceParameter, SymbolId>,
    pub knownness_registers: FxHashMap<InstanceParameter, SymbolId>,
    pub register_inits: FxHashMap<SymbolId, ExprRef>,
    /// All registers, including deterministic loop state, grouped by instance.
    pub registers: FxHashMap<InstanceParameter, SymbolId>,
    /// (Node, action index) -> owning instance. Global Done and shared register
    /// assignments have no single owner.
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

/// prepare and convert each protocol, explicitly simplify its monitor, then
/// build the joint unbounded automaton.
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
        let mut monitor = simplify_monitor(ctx, monitor, symbols);
        opt_iter_count(ctx, &mut monitor, symbols);
        monitors.push(monitor);
    }
    let share = checking_only
        && monitors.len() > 1
        && !monitors.iter().any(|monitor| {
            monitor.graph.nodes().any(|(_, node)| {
                node.actions
                    .iter()
                    .any(|action| matches!(monitor.graph[action.op], Op::Fork))
            })
        });
    let mut monitor = compose_joint_monitor_automaton(ctx, protocols, monitors, symbols)?;
    if share {
        share_registers(ctx, &mut monitor, symbols);
    }
    Ok(monitor)
}

/// Without forks, protocols can reuse the same storage. Candidate first-cycle
/// reads already use their own initial values; only the selected launch writes.
fn share_registers(
    ctx: &mut Context,
    monitor: &mut JointMonitorAutomaton,
    symbols: &mut SymbolTable,
) {
    let graph = &mut monitor.control.graph;
    let mut registers = monitor
        .registers
        .iter()
        .map(|(k, r)| (*k, *r))
        .collect::<Vec<_>>();
    registers.sort();
    let mut counts = FxHashMap::default();
    let mut pool = FxHashMap::default();
    let mut targets = FxHashMap::default();
    let mut replacements = FxHashMap::default();
    let mut initial = FxHashMap::default();
    for ((protocol, slot, _), old) in registers {
        let width = graph.symbol_expr(old).unwrap().get_bv_type(ctx).unwrap();
        let ordinal = counts.entry((protocol, slot, width)).or_insert(0usize);
        let shared = *pool.entry((width, *ordinal)).or_insert_with(|| {
            graph.add_register(
                ctx,
                symbols,
                &format!("$monitor_shared_{width}_{ordinal}"),
                width,
            )
        });
        *ordinal += 1;
        targets.insert(old, shared);
        replacements.insert(
            graph.symbol_expr(old).unwrap(),
            graph.symbol_expr(shared).unwrap(),
        );
        initial
            .entry(shared)
            .or_insert(monitor.register_inits[&old]);
    }

    let nodes = graph.nodes().map(|(n, _)| n).collect::<Vec<_>>();
    let mut owners = FxHashMap::default();
    for node in nodes {
        let mut launches = FxHashMap::default();
        for (index, edge) in graph[node].transitions.iter().enumerate() {
            if let JointTransitionKind::Launch(protocol) =
                monitor.control.transition_kinds[&(node, index)]
            {
                let guard = launches.entry(protocol).or_insert(ctx.get_false());
                *guard = ctx.or(*guard, edge.guard);
            }
        }
        let actions = std::mem::take(&mut graph.node_mut(node).actions);
        let mut writes = FxHashMap::<SymbolId, Assignment>::default();
        for (index, action) in actions.into_iter().enumerate() {
            let owner = monitor.action_owners.get(&(node, index)).copied();
            let guard = remap_expr(ctx, action.guard, &replacements);
            if let Op::Assign(old, assignment) = &graph[action.op] {
                assert_eq!(assignment.dont_care, ctx.get_false());
                let owner = owner.expect("register update needs an owning instance");
                let starts = monitor.control.instances[&node]
                    .iter()
                    .any(|i| i.starts && (i.protocol, i.slot) == owner);
                let default = if starts {
                    monitor.register_inits[old]
                } else {
                    graph.symbol_expr(*old).unwrap()
                };
                let rhs = assignment.to_expr(ctx, default, default);
                let rhs = remap_expr(ctx, rhs, &replacements);
                let selected = if starts {
                    launches[&owner.0]
                } else {
                    ctx.get_true()
                };
                let selected = remap_expr(ctx, selected, &replacements);
                let guard = ctx.and(guard, selected);
                writes
                    .entry(targets[old])
                    .or_insert_with(|| Assignment {
                        dont_care: ctx.get_false(),
                        concretes: Vec::new(),
                    })
                    .concretes
                    .push((guard, rhs));
            } else {
                let op = graph[action.op].remap(ctx, &replacements, &targets);
                let op = graph.o(op);
                if let Some(owner) = owner {
                    owners.insert((node, graph[node].actions.len()), owner);
                }
                graph.push_action(node, Action::new(guard, op));
            }
        }
        let mut writes = writes.into_iter().collect::<Vec<_>>();
        writes.sort_by_key(|(register, _)| *register);
        for (register, assignment) in writes {
            let op = graph.o(Op::Assign(register, assignment));
            graph.push_action(node, Action::new(ctx.get_true(), op));
        }
        for edge in &mut graph.node_mut(node).transitions {
            edge.guard = remap_expr(ctx, edge.guard, &replacements);
        }
    }
    for register in monitor
        .registers
        .values_mut()
        .chain(monitor.value_registers.values_mut())
        .chain(monitor.knownness_registers.values_mut())
    {
        *register = targets[register];
    }
    monitor.register_inits = initial;
    monitor.action_owners = owners;
    graph.register_inits = monitor.register_inits.clone();
    graph.simplify_all_exprs(ctx);
    graph.garbage_collect_ops();
}

/// Assumptions: at a choice node, every protocol tries its first cycle on the current sample.
/// The surviving candidate selects the edge. We assume there is at most one without any checks.
/// TODO: maybe we should ad a runtime check? Then we can say we can also prove with BMC that
/// TODO: the protocols are single-cycle distinguishable.
pub fn compose_joint_monitor_automaton(
    ctx: &mut Context,
    protocols: Vec<Protocol>,
    mut monitors: Vec<MonitorAutomaton>,
    symbols: &mut SymbolTable,
) -> Result<JointMonitorAutomaton, JointMonitorError> {
    // set up the monitor ProtoGraphs, build the control automaton
    let validity = monitors
        .iter_mut()
        .map(|monitor| lower_constraints(ctx, monitor))
        .collect::<Vec<_>>();
    let sources = monitors
        .iter()
        .map(|monitor| monitor.graph.clone())
        .collect::<Vec<_>>();
    let mut control = build_joint_control_automaton(ctx, &protocols, &sources, symbols)?;

    // set up a bad state that self-loops.
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
        register_inits: FxHashMap::default(),
        registers: FxHashMap::default(),
        action_owners: FxHashMap::default(),
    };

    // for each (protocol, slot):
    // - create fresh register symbols included the protocol and slot to prevent collisions
    // record mapping from old register SymbolId to new register SymbolId (`targets`)
    // record mapping from old register expression to new register expression (`substitutions`)
    // record the initial values, ownership (by protocol, slot) and save all the mappings.
    let mut instance_targets = FxHashMap::default();
    let mut instance_exprs = FxHashMap::default();
    for (protocol, monitor) in monitors.iter().enumerate() {
        for slot in 0..result.control.bank_counts[protocol] {
            let mut targets = FxHashMap::default();
            let mut substitutions = FxHashMap::default();
            let mut registers = monitor.register_inits.keys().copied().collect::<Vec<_>>();
            registers.sort();
            for old in registers {
                let base = format!(
                    "{}#{}_{}",
                    symbols[old].name(),
                    slot,
                    result.protocols[protocol].name
                );
                let width = monitor
                    .graph
                    .symbol_expr(old)
                    .unwrap()
                    .get_bv_type(ctx)
                    .unwrap();
                let register = result
                    .control
                    .graph
                    .add_register(ctx, symbols, &base, width);
                let expr = result.control.graph.symbol_expr(register).unwrap();
                targets.insert(old, register);
                result.registers.insert((protocol, slot, old), register);
                substitutions.insert(monitor.graph.symbol_expr(old).unwrap(), expr);
                result
                    .register_inits
                    .insert(register, monitor.register_inits[&old]);
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
    for node in nodes {
        // Collect this node's survival conditions.
        let mut ongoing = ctx.get_true();
        let mut any_launch = ctx.get_false();
        let mut launches = FxHashMap::default();
        let mut edge_values = FxHashMap::default();
        for instance in result.control.instances[&node].clone() {
            // Use the register copies allocated for this protocol and slot.
            let owner = (instance.protocol, instance.slot);
            let monitor = &monitors[instance.protocol];
            let targets = &instance_targets[&owner];
            let mut substitutions = instance_exprs[&owner].clone();
            if instance.starts {
                // Fresh candidates read initial values, even when their slots are reused.
                for (&register, &init) in &monitor.register_inits {
                    substitutions.insert(monitor.graph.symbol_expr(register).unwrap(), init);
                }
            }
            for (old, alias) in crate::ir::joint_automaton::joint_argument_substitutions(
                ctx,
                &monitor.graph,
                &result.protocols[instance.protocol],
                symbols,
                instance.slot,
            ) {
                if let Some(&value) = substitutions.get(&old) {
                    edge_values.insert(alias, value);
                }
            }
            // Copy this instance's actions and track which registers they update.
            let mut assigned = FxHashSet::default();
            let survives = remap_expr(
                ctx,
                validity[instance.protocol][&instance.control],
                &substitutions,
            );
            for action in &monitor.graph[instance.control].actions {
                // Fork and completion are handled by the shared control graph.
                if matches!(monitor.graph[action.op], Op::Fork | Op::Done) {
                    continue;
                }
                let op = monitor.graph[action.op].remap(ctx, &substitutions, targets);
                let guard = remap_expr(ctx, action.guard, &substitutions);
                if let Op::Assign(register, _) = &op {
                    assert_eq!(
                        guard,
                        ctx.get_true(),
                        "monitor assignment guards must be true"
                    );
                    assigned.insert(*register);
                }
                push_owned_action(&mut result, node, owner, guard, op);
            }
            if instance.starts {
                // Reset registers whose entry assignments were removed by simplification.
                let mut registers = monitor.register_inits.iter().collect::<Vec<_>>();
                registers.sort_by_key(|(register, _)| **register);
                for (&old, &init) in registers {
                    let register = targets[&old];
                    if !assigned.contains(&register) {
                        let assignment =
                            Assignment::concrete(ctx.get_false(), ctx.get_true(), init);
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
            // Require each instance's constraints to hold on the current sample
            if instance.starts {
                any_launch = ctx.or(any_launch, survives);
                launches.insert(instance.protocol, survives);
            } else {
                ongoing = ctx.and(ongoing, survives);
            }
        }
        // Require all ongoing instances to survive, plus a candidate at choice nodes.
        let required = if result.control.choice_slots.contains_key(&node) {
            ctx.and(ongoing, any_launch)
        } else {
            ongoing
        };
        // Require ongoing instances to survive before taking a normal edge.
        for (index, edge) in result
            .control
            .graph
            .node_mut(node)
            .transitions
            .iter_mut()
            .enumerate()
        {
            // Select launches by their constraints; completion uses Done rather than a stop edge.
            let selected = match result.control.transition_kinds[&(node, index)] {
                JointTransitionKind::Launch(protocol) => launches[&protocol],
                JointTransitionKind::Stop => ctx.get_false(),
                JointTransitionKind::Continue => ctx.get_true(),
            };
            let survives = ctx.and(ongoing, selected);
            let guard = remap_expr(ctx, edge.guard, &edge_values);
            edge.guard = ctx.and(guard, survives);
        }
        // Enter the bad state if an ongoing instance dies or all choice candidates fail.
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
    }
    result.control.graph.simplify_all_exprs(ctx);
    Ok(result)
}

/// Remove monitor assertions and collect the validity condition for each source node.
/// A failed constraint takes the joint monitor to the bad state
fn lower_constraints(
    ctx: &mut Context,
    monitor: &mut MonitorAutomaton,
) -> FxHashMap<NodeId, ExprRef> {
    let graph = &mut monitor.graph;
    let nodes = graph.nodes().map(|(node, _)| node).collect::<Vec<_>>();
    let mut validity = FxHashMap::default();
    for node in nodes {
        let mut failed = ctx.get_false();
        let mut actions = Vec::new();
        for action in graph[node].actions.clone() {
            if let Some(failure) = graph[action.op].assertion_failure(ctx, action.guard) {
                failed = ctx.or(failed, failure);
            } else {
                actions.push(action);
            }
        }
        let failed = simplify_guarded(ctx, &mut graph.simplifier, failed, ctx.get_true());
        validity.insert(node, ctx.not(failed));
        graph.node_mut(node).actions = actions;
    }

    validity
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
mod tests {
    use super::*;
    use crate::frontend::{diagnostic::DiagnosticHandler, require_single_module};
    use baa::{BitVecOps, BitVecValue};
    use patronus::expr::{Expr, SymbolValueStore, eval_expr};

    fn build(source: &str, checking: bool) -> (Context, SymbolTable, JointMonitorAutomaton) {
        let file = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(file.path(), source).unwrap();
        let (mut symbols, modules) = crate::frontend(
            &[file.path()],
            &mut DiagnosticHandler::default(),
            false,
            false,
        )
        .unwrap();
        let module = require_single_module(modules, &[file.path()]).unwrap();
        let mut ctx = Context::default();
        let monitor = build_monitor(&mut ctx, module.protos, &mut symbols, checking).unwrap();
        (ctx, symbols, monitor)
    }

    const TWO_PROTOCOLS: &str = r#"
        interface Bus { in kind: u1, in x: u8, out ack: u1 }
        prot a<DUT: Bus>(v: u8) {
            DUT.kind := 1'b0; DUT.x := v; step();
            DUT.x := v;
            while !DUT.ack { step(); }
            step();
        }
        prot b<DUT: Bus>(v: u8) {
            DUT.kind := 1'b1; DUT.x := v + 8'b00000001; step();
            DUT.x := v;
            while !DUT.ack { step(); }
            step();
        }
    "#;

    fn value(ctx: &Context, store: &SymbolValueStore, e: ExprRef) -> BitVecValue {
        eval_expr(ctx, store, e).try_into().unwrap()
    }

    #[test]
    fn shared_first_cycle_commits_only_the_selected_candidate() {
        let (_, _, capturing) = build(TWO_PROTOCOLS, false);
        assert_eq!(capturing.register_inits.len(), 2);
        let (mut ctx, symbols, monitor) = build(TWO_PROTOCOLS, true);
        assert_eq!(monitor.register_inits.len(), 1);
        assert_eq!(
            monitor
                .registers
                .values()
                .copied()
                .collect::<FxHashSet<_>>()
                .len(),
            1
        );
        let graph = &monitor.control.graph;
        // Repeated protocol switches must ignore the previous transaction's data.
        for corrupt in [false, true] {
            let mut store = SymbolValueStore::default();
            let mut defined = FxHashSet::default();
            for &e in graph.symbol_expr.values() {
                if matches!(ctx[e], Expr::BVSymbol { .. }) && defined.insert(e) {
                    store.define_bv(e, &BitVecValue::zero(e.get_bv_type(&ctx).unwrap()));
                }
            }
            for (&register, &init) in &monitor.register_inits {
                store.update(
                    graph.symbol_expr(register).unwrap(),
                    eval_expr(&ctx, &store, init),
                );
            }
            let mut node = graph.entry;
            for transaction in 0..12 {
                let kind = transaction % 2;
                let first = 17 + transaction;
                for cycle in 0..2 {
                    for (&symbol, &e) in &graph.symbol_expr {
                        if !symbols[symbol].is_port() {
                            continue;
                        }
                        let input = match symbols[symbol].name() {
                            "kind" => kind,
                            "x" => {
                                if cycle == 0 {
                                    first
                                } else {
                                    let expected =
                                        if kind == 0 { first } else { (first - 1) & 255 };
                                    if corrupt { expected ^ 1 } else { expected }
                                }
                            }
                            "ack" => 1,
                            _ => continue,
                        };
                        store.update_bv(
                            e,
                            &BitVecValue::from_u64(input, e.get_bv_type(&ctx).unwrap()),
                        );
                    }
                    let edges = graph[node]
                        .transitions
                        .iter()
                        .filter(|edge| !value(&ctx, &store, edge.guard).is_zero())
                        .collect::<Vec<_>>();
                    assert_eq!(edges.len(), 1);
                    let next = edges[0].target;
                    let mut writes = Vec::new();
                    for action in &graph[node].actions {
                        if value(&ctx, &store, action.guard).is_zero() {
                            continue;
                        }
                        if let Op::Assign(register, assignment) = &graph[action.op] {
                            let held = graph.symbol_expr(*register).unwrap();
                            let rhs = assignment.to_expr(&mut ctx, held, held);
                            writes.push((held, eval_expr(&ctx, &store, rhs)));
                        }
                    }
                    for (register, value) in writes {
                        store.update(register, value);
                    }
                    node = next;
                    assert_eq!(node == monitor.bad_state, corrupt && cycle == 1);
                }
                if corrupt {
                    break;
                }
            }
        }
    }

    #[test]
    fn checking_monitor_with_forks_keeps_separate_registers() {
        let source = TWO_PROTOCOLS.replace(
            "while !DUT.ack { step(); }\n            step();",
            "fork(); step();\n            DUT.x := v; step();",
        );
        let (_, symbols, monitor) = build(&source, true);
        assert!(
            monitor
                .registers
                .values()
                .all(|r| !symbols[*r].name().starts_with("$monitor_shared_"))
        );
        assert_eq!(
            monitor.register_inits.len(),
            monitor
                .registers
                .values()
                .copied()
                .collect::<FxHashSet<_>>()
                .len()
        );
    }
}
