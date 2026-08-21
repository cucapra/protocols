use crate::PortId;
use crate::backends::transition_system::{
    CoreLoweredSystem, IfThenExpr, if_thens_to_ite, lower_proto_graph_to_transition_system,
};
use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolTable, Type};
use crate::ir::meta_automaton::MetaAutomaton;
use crate::ir::meta_lowering::lower_steady_driver_nfa_with_choice_instances;
use crate::ir::propagate_assigns::propagate_assignments;
use crate::ir::proto_graph::{NodeId, Op};
use crate::ir::reaching_defs::reaching_definitions;
use baa::WidthInt;
use patronus::expr::{Context, ExprRef, TypeCheck, simple_transform_expr};
use patronus::system::{State, TransitionSystem};
use rustc_hash::FxHashMap;
use std::borrow::Cow;

pub struct MetaLoweredSystemResult {
    pub ctx: Context,
    pub ts: TransitionSystem,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub protocol_inputs: FxHashMap<(usize, crate::frontend::symbol::SymbolId), ExprRef>,
    pub node_symbol: ExprRef,
    pub done_state: ExprRef,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
    pub node_choice: ExprRef,
    pub fork_ready: ExprRef,
    pub fork_banks: Vec<ExprRef>,
    pub heads: Vec<ExprRef>,
    pub meta: MetaAutomaton,
}

fn replace_expr(ctx: &mut Context, expr: ExprRef, old: ExprRef, new: ExprRef) -> ExprRef {
    simple_transform_expr(ctx, expr, |_ctx, candidate, _children| {
        (candidate == old).then_some(new)
    })
}

fn mod_add(ctx: &mut Context, value: ExprRef, amount: usize, modulus: usize) -> ExprRef {
    if modulus == 1 || amount % modulus == 0 {
        return value;
    }
    let width = value.get_bv_type(ctx).unwrap();
    let amount = amount % modulus;
    let amount_expr = ctx.bit_vec_val(amount, width);
    let threshold = ctx.bit_vec_val(modulus - amount, width);
    let wrapped = ctx.sub(value, threshold);
    let normal = ctx.add(value, amount_expr);
    let overflow = ctx.greater_or_equal(value, threshold);
    ctx.ite(overflow, wrapped, normal)
}

fn choice_guard(
    ctx: &mut Context,
    node_choice: ExprRef,
    protocol: usize,
    protocol_count: usize,
    width: WidthInt,
) -> ExprRef {
    if protocol_count == 1 {
        ctx.get_true()
    } else {
        let value = ctx.bit_vec_val(protocol, width);
        ctx.equal(node_choice, value)
    }
}

fn fork_ready(ctx: &mut Context, core: &CoreLoweredSystem) -> ExprRef {
    let mut forks = Vec::new();
    for id in &core.reachable_nodes {
        let value = ctx.bit_vec_val(id.as_u32(), core.node_id_width);
        let node = ctx.equal(core.node_symbol, value);
        for action in &core.pg[*id].actions {
            if matches!(core.pg[action.op], Op::Fork) {
                forks.push(IfThenExpr {
                    if_cond: ctx.and(node, action.guard),
                    then: ctx.bit_vec_val(1, 1),
                });
            }
        }
    }
    let zero = ctx.bit_vec_val(0, 1);
    if_thens_to_ite(forks, ctx, zero)
}

pub fn into_meta_transition_system(
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    ts: TransitionSystem,
    symbol_to_port: FxHashMap<crate::frontend::symbol::SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    expr_ctx: Context,
) -> MetaLoweredSystemResult {
    assert!(!protocols.is_empty());
    let (mut pg, meta, node_choice, choice_instances) =
        lower_steady_driver_nfa_with_choice_instances(protocols.clone(), symbols, expr_ctx);
    let rd = reaching_definitions(&mut pg, symbols);
    propagate_assignments(&mut pg, symbols, &rd);
    let ctx = std::mem::take(&mut pg.expr_ctx);
    let core = lower_proto_graph_to_transition_system(
        pg,
        ctx,
        ts,
        symbol_to_port,
        port_to_expr,
        symbols,
    );
    lower_meta_core(core, protocols, symbols, meta, node_choice, choice_instances)
}

fn lower_meta_core(
    core: CoreLoweredSystem,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
    meta: MetaAutomaton,
    node_choice: ExprRef,
    choice_instances: FxHashMap<NodeId, usize>,
) -> MetaLoweredSystemResult {
    let mut ctx = core.ctx.clone();
    let mut ready = fork_ready(&mut ctx, &core);
    for &node in choice_instances.keys() {
        let node_value = ctx.bit_vec_val(node.as_u32(), core.node_id_width);
        let node_guard = ctx.equal(core.node_symbol, node_value);
        ready = ctx.or(ready, node_guard);
    }
    let mut ts = core.ts;
    let mut protocol_inputs = FxHashMap::default();
    let mut heads = Vec::new();
    let mut bank_states = Vec::new();
    let mut bank_counts = meta.bank_counts.clone();
    for count in &mut bank_counts {
        *count = (*count).max(1);
    }

    let width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };
    ts.add_input(&ctx, node_choice);

    for (protocol_id, protocol) in protocols.iter().enumerate() {
        let bank_count = bank_counts[protocol_id];
        let head_width = if bank_count <= 1 {
            1
        } else {
            usize::BITS - (bank_count - 1).leading_zeros()
        };
        let head = ctx.bv_symbol(&format!("head_{}", protocol.name), head_width);
        heads.push(head);
        let mut banks = Vec::new();
        for bank in 0..bank_count {
            let state_args = protocol
                .args
                .iter()
                .map(|arg| {
                    let symbol = arg.symbol();
                    let name = symbols[symbol].name();
                    let width = match symbols[symbol].tpe() {
                        Type::BitVec(width) => width,
                        other => panic!("unsupported argument type {other:?}"),
                    };
                    ctx.bv_symbol(&format!("{name}#bank{bank}_{}", protocol.name), width)
                })
                .collect::<Vec<_>>();
            banks.push(state_args);
        }
        bank_states.push(banks);
        for arg in &protocol.args {
            let symbol = arg.symbol();
            let name = symbols[symbol].name();
            let arg_width = match symbols[symbol].tpe() {
                Type::BitVec(width) => width,
                other => panic!("unsupported argument type {other:?}"),
            };
            let input = ctx.bv_symbol(&format!("{name}_{}", protocol.name), arg_width);
            ts.add_input(&ctx, input);
            protocol_inputs.insert((protocol_id, symbol), input);
        }
    }

    let mut capture = bank_counts
        .iter()
        .map(|&count| vec![ctx.get_false(); count])
        .collect::<Vec<_>>();
    let mut fork_banks = Vec::new();
    for protocol_id in 0..protocols.len() {
        let selected = choice_guard(&mut ctx, node_choice, protocol_id, protocols.len(), width);
        let mut bank_expr = ctx.bit_vec_val(0, heads[protocol_id].get_bv_type(&ctx).unwrap());
        for (&node, &instance) in &choice_instances {
            let node_value = ctx.bit_vec_val(node.as_u32(), core.node_id_width);
            let node_guard = ctx.equal(core.node_symbol, node_value);
            for head_value in 0..bank_counts[protocol_id] {
                let head_width = heads[protocol_id].get_bv_type(&ctx).unwrap();
                let head_literal = ctx.bit_vec_val(head_value, head_width);
                let head_guard = ctx.equal(heads[protocol_id], head_literal);
                let selected_head = ctx.and(selected, head_guard);
                let selected_node = ctx.and(node_guard, selected_head);
                let guard = ctx.and(ready, selected_node);
                let bank = (instance + head_value) % bank_counts[protocol_id];
                capture[protocol_id][bank] = ctx.or(capture[protocol_id][bank], guard);
                let physical = mod_add(&mut ctx, heads[protocol_id], instance, bank_counts[protocol_id]);
                bank_expr = ctx.ite(guard, physical, bank_expr);
            }
        }
        fork_banks.push(bank_expr);
    }

    let mut replacements = Vec::new();
    for (protocol_id, protocol) in protocols.iter().enumerate() {
        for instance in 0..bank_counts[protocol_id] {
            for arg in &protocol.args {
                let symbol = arg.symbol();
                let name = symbols[symbol].name();
                let arg_width = match symbols[symbol].tpe() {
                    Type::BitVec(width) => width,
                    _ => panic!("unsupported argument type"),
                };
                let old = ctx.bv_symbol(&format!("{name}#{instance}_{}", protocol.name), arg_width);
                let mut read = ctx.zero(arg_width as WidthInt);
                for head_value in 0..bank_counts[protocol_id] {
                    let bank = (instance + head_value) % bank_counts[protocol_id];
                    let bank_value = bank_states[protocol_id][bank]
                        [protocol.args.iter().position(|a| a.symbol() == symbol).unwrap()];
                    let input = protocol_inputs[&(protocol_id, symbol)];
                    let value = ctx.ite(capture[protocol_id][bank], input, bank_value);
                    let head_literal = ctx.bit_vec_val(
                        head_value,
                        heads[protocol_id].get_bv_type(&ctx).unwrap(),
                    );
                    let head_eq = ctx.equal(heads[protocol_id], head_literal);
                    read = ctx.ite(head_eq, value, read);
                }
                replacements.push((old, read));
            }
        }
    }

    for (protocol_id, banks) in bank_states.iter().enumerate() {
        let head_width = heads[protocol_id].get_bv_type(&ctx).unwrap();
        let zero = ctx.bit_vec_val(0, head_width);
        let mut head_next = heads[protocol_id];
        for id in &core.reachable_nodes {
            let node_value = ctx.bit_vec_val(id.as_u32(), core.node_id_width);
            let node_guard = ctx.equal(core.node_symbol, node_value);
            for transition in &core.pg[*id].transitions {
                let Some(amount) = transition
                    .rotations
                    .iter()
                    .find(|rotation| rotation.protocol == protocols[protocol_id].name)
                    .map(|rotation| rotation.amount)
                else {
                    continue;
                };
                let guard = ctx.and(node_guard, transition.guard);
                let next = mod_add(&mut ctx, heads[protocol_id], amount, bank_counts[protocol_id]);
                head_next = ctx.ite(guard, next, head_next);
            }
        }
        ts.add_state(&ctx, State { symbol: heads[protocol_id], init: Some(zero), next: Some(head_next) });
        for (bank, args) in banks.iter().enumerate() {
            for (arg_index, state_arg) in args.iter().enumerate() {
                let input = protocol_inputs[&(protocol_id, protocols[protocol_id].args[arg_index].symbol())];
                let next = ctx.ite(capture[protocol_id][bank], input, *state_arg);
                let init = ctx.zero(state_arg.get_bv_type(&ctx).unwrap());
                ts.add_state(&ctx, State { symbol: *state_arg, init: Some(init), next: Some(next) });
            }
        }
    }

    for (old, new) in &replacements {
        ts.update_expressions(|expr| Some(replace_expr(&mut ctx, expr, *old, *new)));
    }

    ts.add_output(&mut ctx, Cow::from("fork_ready"), ready);
    for (protocol, bank) in protocols.iter().zip(fork_banks.iter()) {
        ts.add_output(&mut ctx, Cow::from(format!("fork_bank_{}", protocol.name)), *bank);
    }

    let mut port_to_expr = core.port_to_expr;
    for expr in port_to_expr.values_mut() {
        for (old, new) in &replacements {
            *expr = replace_expr(&mut ctx, *expr, *old, *new);
        }
    }

    MetaLoweredSystemResult {
        ctx,
        ts,
        port_to_expr,
        protocol_inputs,
        node_symbol: core.node_symbol,
        done_state: core.done_state,
        external_assert_state: core.external_assert_state,
        internal_assert_state: core.internal_assert_state,
        is_dont_care: core.is_dont_care,
        node_choice,
        fork_ready: ready,
        fork_banks,
        heads,
        meta,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PatronusSim;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::{frontend, require_single_module};
    use patronus::mc::bmc;
    use patronus::smt::{Solver, Z3};

    fn add_d1_banked_driver_bmc(add_constraint: bool) -> patronus::mc::ModelCheckResult {
        let mut handler = DiagnosticHandler::default();
        let (symbols, modules) = frontend(&["../tests/adders/adder_d1/add_d1.prot"], &mut handler, false)
            .unwrap();
        let module = require_single_module(modules, &["../tests/adders/adder_d1/add_d1.prot"]).unwrap();
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
        let port_expr_refs = FxHashMap::from_iter(
            sim.ios()
                .filter_map(|port| sim.get_port_expr(port).map(|expr| (port, expr))),
        );
        let mut result = into_meta_transition_system(
            protocols,
            &symbols,
            sim.sys.clone(),
            sim.port_map.clone(),
            port_expr_refs,
            sim.ctx.clone(),
        );

        assert!(result
            .ts
            .inputs
            .iter()
            .all(|input| !result.ctx.get_symbol_name(*input).unwrap().contains("#bank")));
        assert!(result
            .ts
            .states
            .iter()
            .any(|state| result.ctx.get_symbol_name(state.symbol).unwrap().contains("#bank0_add")));

        let add = module.protos.iter().find(|protocol| protocol.name == "add").unwrap();
        let a = result.protocol_inputs[&(0, add.args[0].symbol())];
        let b = result.protocol_inputs[&(0, add.args[1].symbol())];
        let s = result.protocol_inputs[&(0, add.args[2].symbol())];
        let sum = result.ctx.add(a, b);
        if add_constraint {
            result.ts.constraints.push(result.ctx.equal(s, sum));
        }
        // The backend registers external/internal assertion states as bad
        // states; this is an actual assertion check, not a dummy property.
        assert_eq!(result.ts.bad_states.len(), 2);

        let mut solver = Z3.start(None).unwrap();
        bmc(&mut result.ctx, &mut solver, &result.ts, true, false, 30).unwrap()
    }

    #[test]
    fn add_d1_banked_driver_bmc_with_adder_constraint() {
        let check = add_d1_banked_driver_bmc(true);
        assert!(matches!(check, patronus::mc::ModelCheckResult::Success));
    }

    #[test]
    fn add_d1_banked_driver_bmc_without_adder_constraint_fails() {
        let check = add_d1_banked_driver_bmc(false);
        assert!(matches!(check, patronus::mc::ModelCheckResult::Fail(_)));
    }
}
