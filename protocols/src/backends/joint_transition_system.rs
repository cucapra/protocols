use std::borrow::Cow;

use patronus::expr::{Context, ExprRef, TypeCheck};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashMap;

use crate::PortId;
use crate::backends::protocol_banks::{mod_add, read_bank};
use crate::backends::transition_system::{
    CoreLoweredSystem, lower_proto_graph_to_transition_system, replace_expr,
};
use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolTable, Type};
use crate::ir::joint_automaton::ProtocolId;
use crate::ir::joint_driver::JointDriverAutomaton;
use crate::ir::proto_graph::NodeId;

pub struct JointTransitionSystemResult {
    pub ts: TransitionSystem,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub protocol_inputs: FxHashMap<(ProtocolId, SymbolId), ExprRef>,
    pub node_symbol: ExprRef,
    pub done_state: ExprRef,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
    pub choice_valid: ExprRef,
    pub protocol_choice: ExprRef,
    pub transaction_ready: ExprRef,
    pub transaction_banks: Vec<ExprRef>,
    pub heads: Vec<ExprRef>,
}

struct JointMetadata {
    protocols: Vec<Protocol>,
    choice_valid: ExprRef,
    protocol_choice: ExprRef,
    choice_slots: FxHashMap<NodeId, Vec<usize>>,
    bank_counts: Vec<usize>,
}

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

fn choice_ready(
    ctx: &mut Context,
    core: &CoreLoweredSystem,
    // choice node -> next available transaction slot for each protocol (Vec indexed by protocol id)
    // Ex. node1 -> [2, 0] means proto-A would use slot 2, proto-B would use slot 0.
    choice_slots: &FxHashMap<NodeId, Vec<usize>>,
) -> ExprRef {
    choice_slots.keys().fold(ctx.get_false(), |ready, node| {
        let value = ctx.bit_vec_val(node.as_u32(), core.node_id_width);
        let at_node = ctx.equal(core.node_symbol, value);
        ctx.or(ready, at_node)
    })
}

/// Add the argument-bank state and transaction handshake to a joint driver.
pub fn into_joint_transition_system(
    ctx: &mut Context,
    driver: JointDriverAutomaton,
    symbols: &SymbolTable,
    ts: TransitionSystem,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
) -> JointTransitionSystemResult {
    let JointDriverAutomaton {
        graph,
        protocols,
        choice_valid,
        protocol_choice,
        choice_slots,
        bank_counts,
    } = driver;
    let core = lower_proto_graph_to_transition_system(
        ctx,
        graph,
        ts,
        symbol_to_port,
        port_to_expr,
        symbols,
    );
    lower_joint_core(
        ctx,
        core,
        JointMetadata {
            protocols,
            choice_valid,
            protocol_choice,
            choice_slots,
            bank_counts,
        },
        symbols,
    )
}

fn lower_joint_core(
    ctx: &mut Context,
    core: CoreLoweredSystem,
    driver: JointMetadata,
    symbols: &SymbolTable,
) -> JointTransitionSystemResult {
    let ready = choice_ready(ctx, &core, &driver.choice_slots);
    let mut ts = core.ts;
    ts.add_input(ctx, driver.choice_valid);
    ts.add_input(ctx, driver.protocol_choice);

    let valid_one = ctx.bit_vec_val(1, 1);
    let valid = ctx.equal(driver.choice_valid, valid_one);
    let mut protocol_inputs = FxHashMap::default();
    let mut heads = Vec::with_capacity(driver.protocols.len());
    let mut bank_states = Vec::with_capacity(driver.protocols.len());

    for (protocol_id, protocol) in driver.protocols.iter().enumerate() {
        let bank_count = driver.bank_counts[protocol_id];
        let head_width = if bank_count <= 1 {
            1
        } else {
            usize::BITS - (bank_count - 1).leading_zeros()
        };
        let head = ctx.bv_symbol(&format!("joint.head_{}", protocol.name), head_width);
        heads.push(head);

        let mut banks = Vec::with_capacity(bank_count);
        for bank in 0..bank_count {
            let args: Vec<ExprRef> = protocol
                .args
                .iter()
                .map(|arg| {
                    let symbol = arg.symbol();
                    let name = symbols[symbol].name();
                    let width = match symbols[symbol].tpe() {
                        Type::BitVec(width) => width,
                        other => panic!("unsupported joint-driver argument type {other:?}"),
                    };
                    ctx.bv_symbol(&format!("joint.{name}#bank{bank}_{}", protocol.name), width)
                })
                .collect();
            banks.push(args);
        }
        bank_states.push(banks);

        for arg in &protocol.args {
            let symbol = arg.symbol();
            let name = symbols[symbol].name();
            let width = match symbols[symbol].tpe() {
                Type::BitVec(width) => width,
                other => panic!("unsupported joint-driver argument type {other:?}"),
            };
            let input = ctx.bv_symbol(&format!("joint.{name}_{}", protocol.name), width);
            ts.add_input(ctx, input);
            protocol_inputs.insert((protocol_id, symbol), input);
        }
    }

    let mut capture = driver
        .bank_counts
        .iter()
        .map(|&count| vec![ctx.get_false(); count])
        .collect::<Vec<_>>();
    let mut transaction_banks = Vec::with_capacity(driver.protocols.len());

    for protocol_id in 0..driver.protocols.len() {
        let selected = selector_guard(
            ctx,
            driver.protocol_choice,
            protocol_id,
            driver.protocols.len(),
        );
        let selected_valid = ctx.and(valid, selected);
        let head_width = heads[protocol_id].get_bv_type(ctx).unwrap();
        let mut selected_bank = ctx.bit_vec_val(0, head_width);
        for (&node, slots) in &driver.choice_slots {
            let slot = slots[protocol_id];
            let node_value = ctx.bit_vec_val(node.as_u32(), core.node_id_width);
            let node_guard = ctx.equal(core.node_symbol, node_value);
            let launch = ctx.and(node_guard, selected_valid);
            let physical = mod_add(
                ctx,
                heads[protocol_id],
                slot,
                driver.bank_counts[protocol_id],
            );
            selected_bank = ctx.ite(launch, physical, selected_bank);

            for head_value in 0..driver.bank_counts[protocol_id] {
                let head_literal = ctx.bit_vec_val(head_value, head_width);
                let at_head = ctx.equal(heads[protocol_id], head_literal);
                let guard = ctx.and(launch, at_head);
                let bank = (head_value + slot) % driver.bank_counts[protocol_id];
                capture[protocol_id][bank] = ctx.or(capture[protocol_id][bank], guard);
            }
        }
        transaction_banks.push(selected_bank);
    }

    let mut replacements = Vec::new();
    for (protocol_id, protocol) in driver.protocols.iter().enumerate() {
        for slot in 0..driver.bank_counts[protocol_id] {
            for (arg_index, arg) in protocol.args.iter().enumerate() {
                let symbol = arg.symbol();
                let name = symbols[symbol].name();
                let width = match symbols[symbol].tpe() {
                    Type::BitVec(width) => width,
                    _ => panic!("unsupported joint-driver argument type"),
                };
                let old = ctx.bv_symbol(&format!("joint.{name}#{slot}_{}", protocol.name), width);
                let input = protocol_inputs[&(protocol_id, symbol)];
                let values = bank_states[protocol_id]
                    .iter()
                    .enumerate()
                    .map(|(bank, args)| ctx.ite(capture[protocol_id][bank], input, args[arg_index]))
                    .collect::<Vec<_>>();
                let read = read_bank(ctx, heads[protocol_id], slot, &values);
                replacements.push((old, read));
            }
        }
    }

    for (protocol_id, banks) in bank_states.iter().enumerate() {
        let head_width = heads[protocol_id].get_bv_type(ctx).unwrap();
        let zero = ctx.bit_vec_val(0, head_width);
        let mut head_next = heads[protocol_id];
        for node in &core.reachable_nodes {
            let node_value = ctx.bit_vec_val(node.as_u32(), core.node_id_width);
            let node_guard = ctx.equal(core.node_symbol, node_value);
            for transition in &core.pg[*node].transitions {
                let Some(amount) = transition
                    .rotations
                    .iter()
                    .find(|rotation| rotation.protocol == driver.protocols[protocol_id].name)
                    .map(|rotation| rotation.amount)
                else {
                    continue;
                };
                let transition_guard = ctx.and(node_guard, transition.guard);
                let next = mod_add(
                    ctx,
                    heads[protocol_id],
                    amount,
                    driver.bank_counts[protocol_id],
                );
                head_next = ctx.ite(transition_guard, next, head_next);
            }
        }
        ts.add_state(
            ctx,
            State {
                symbol: heads[protocol_id],
                init: Some(zero),
                next: Some(head_next),
            },
        );

        for (bank, args) in banks.iter().enumerate() {
            for (arg_index, state_arg) in args.iter().enumerate() {
                let symbol = driver.protocols[protocol_id].args[arg_index].symbol();
                let input = protocol_inputs[&(protocol_id, symbol)];
                let next = ctx.ite(capture[protocol_id][bank], input, *state_arg);
                let init = ctx.zero(state_arg.get_bv_type(ctx).unwrap());
                ts.add_state(
                    ctx,
                    State {
                        symbol: *state_arg,
                        init: Some(init),
                        next: Some(next),
                    },
                );
            }
        }
    }

    for (old, new) in &replacements {
        ts.update_expressions(|expr| Some(replace_expr(ctx, expr, *old, *new)));
    }

    ts.add_output(ctx, Cow::from("transaction_ready"), ready);
    for (protocol, bank) in driver.protocols.iter().zip(&transaction_banks) {
        ts.add_output(
            ctx,
            Cow::from(format!("transaction_bank_{}", protocol.name)),
            *bank,
        );
    }

    let mut port_to_expr = core.port_to_expr;
    for expr in port_to_expr.values_mut() {
        for (old, new) in &replacements {
            *expr = replace_expr(ctx, *expr, *old, *new);
        }
    }

    JointTransitionSystemResult {
        ts,
        port_to_expr,
        protocol_inputs,
        node_symbol: core.node_symbol,
        done_state: core.done_state,
        external_assert_state: core.external_assert_state,
        internal_assert_state: core.internal_assert_state,
        is_dont_care: core.is_dont_care,
        choice_valid: driver.choice_valid,
        protocol_choice: driver.protocol_choice,
        transaction_ready: ready,
        transaction_banks,
        heads,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatronusSim;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::{frontend, require_single_module};
    use crate::ir::joint_driver::build_joint_driver_automaton;
    use patronus::mc::bmc;
    use patronus::smt::{Solver, Z3};

    fn joint_add_d1_bmc(add_constraint: bool) -> patronus::mc::ModelCheckResult {
        let filename = "../tests/adders/adder_d1/add_d1.prot";
        let mut handler = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let protocols = module
            .protos
            .iter()
            .filter(|protocol| protocol.name == "add")
            .cloned()
            .collect::<Vec<_>>();
        let sim = PatronusSim::new(
            &["../tests/adders/adder_d1/add_d1.v"],
            Some("adder_d1"),
            &module,
            None,
        )
        .unwrap();
        let mut ctx = sim.ctx.clone();
        let port_expr_refs = FxHashMap::from_iter(
            sim.ios()
                .filter_map(|port| sim.get_port_expr(port).map(|expr| (port, expr))),
        );
        let driver =
            build_joint_driver_automaton(&mut ctx, &module, protocols, &mut symbols).unwrap();
        let mut result = into_joint_transition_system(
            &mut ctx,
            driver,
            &symbols,
            sim.sys.clone(),
            sim.port_map.clone(),
            port_expr_refs,
        );

        assert!(
            result
                .ts
                .inputs
                .iter()
                .all(|input| { !ctx.get_symbol_name(*input).unwrap().contains("#bank") })
        );
        assert!(result.ts.states.iter().any(|state| {
            ctx.get_symbol_name(state.symbol)
                .unwrap()
                .contains("#bank0_add")
        }));

        let add = module
            .protos
            .iter()
            .find(|protocol| protocol.name == "add")
            .unwrap();
        let a = result.protocol_inputs[&(0, add.args[0].symbol())];
        let b = result.protocol_inputs[&(0, add.args[1].symbol())];
        let s = result.protocol_inputs[&(0, add.args[2].symbol())];
        if add_constraint {
            let sum = ctx.add(a, b);
            result.ts.constraints.push(ctx.equal(s, sum));
        }

        assert_eq!(result.ts.bad_states.len(), 2);
        let mut solver = Z3.start(None).unwrap();
        bmc(&mut ctx, &mut solver, &result.ts, true, false, 8).unwrap()
    }

    #[test]
    fn joint_add_d1_banked_driver_is_safe_with_correct_results() {
        assert!(matches!(
            joint_add_d1_bmc(true),
            patronus::mc::ModelCheckResult::Success
        ));
    }

    #[test]
    fn joint_add_d1_banked_driver_can_detect_bad_results() {
        assert!(matches!(
            joint_add_d1_bmc(false),
            patronus::mc::ModelCheckResult::Fail(_)
        ));
    }
}
