//! Lower an unbounded monitor without a DUT model or transaction selectors.

use std::borrow::Cow;

use patronus::expr::{Context, ExprRef, TypeCheck};
use patronus::system::{State, TransitionSystem};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::backends::protocol_banks::{mod_add, read_bank};
use crate::frontend::Module;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::joint_monitor::JointMonitorAutomaton;
use crate::ir::proto_graph::{Op, remap_expr};

pub struct MonitorTransitionSystemResult {
    pub ts: TransitionSystem,
    /// All protocol pin aliases map to the input for their common DUT field.
    pub pin_inputs: FxHashMap<SymbolId, ExprRef>,
    pub node_symbol: ExprRef,
    pub bad: ExprRef,
    pub internal_error: ExprRef,
    pub heads: Vec<ExprRef>,
    /// reads of FIFO registers, using the current bank heads.
    pub register_reads: FxHashMap<SymbolId, ExprRef>,
}

/// set up the monitor ring-buffers with value, knownness registers and the liveness register
fn bank_fields(monitor: &JointMonitorAutomaton) -> Vec<Vec<Vec<SymbolId>>> {
    let mut owned = FxHashSet::default();
    let fields = monitor
        .protocols
        .iter()
        .enumerate()
        .map(|(protocol, _)| {
            let count = monitor.control.bank_counts[protocol];
            let mut registers = monitor
                .registers
                .keys()
                .filter_map(|&(p, slot, r)| (p == protocol && slot == 0).then_some(r))
                .collect::<Vec<_>>();
            registers.sort();
            let fields = registers
                .into_iter()
                .map(|r| {
                    (0..count)
                        .map(|slot| monitor.registers[&(protocol, slot, r)])
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            for field in &fields {
                for &register in field {
                    assert!(
                        owned.insert(register),
                        "monitor register has multiple owners"
                    );
                }
            }
            fields
        })
        .collect();
    assert_eq!(owned.len(), monitor.register_inits.len());
    assert!(
        monitor
            .register_inits
            .keys()
            .all(|register| owned.contains(register))
    );
    fields
}

pub fn into_monitor_transition_system(
    ctx: &mut Context,
    monitor: &JointMonitorAutomaton,
    module: &Module,
    symbols: &SymbolTable,
) -> MonitorTransitionSystemResult {
    let graph = &monitor.control.graph;
    let mut ts = TransitionSystem::new(format!("monitor_{}", module.name));
    let mut pin_inputs = FxHashMap::default();
    let mut reads = FxHashMap::default();

    // for a monitor, input and output pins of the DUT are inputs to the transition system.
    for (index, pin) in module.pins.iter().enumerate() {
        let input = ctx.bv_symbol(&format!("monitor.pin.{}", pin.name()), pin.bitwidth());
        ts.add_input(ctx, input);
        for mapping in &module.proto_pin_map {
            let symbol = mapping[index];
            pin_inputs.insert(symbol, input);
            if let Some(expr) = graph.symbol_expr(symbol) {
                reads.insert(expr, input);
            }
        }
    }

    let fields = bank_fields(monitor);
    // exprRefs for the heads of the ring buffers
    let heads = monitor
        .protocols
        .iter()
        .enumerate()
        .map(|(protocol, proto)| {
            let count = monitor.control.bank_counts[protocol];
            let width = (usize::BITS - (count - 1).leading_zeros()).max(1);
            ctx.bv_symbol(&format!("monitor.head_{}", proto.name), width)
        })
        .collect::<Vec<_>>();
    let mut register_reads = FxHashMap::default();
    let mut owners = FxHashMap::default();
    let mut banks = Vec::new();
    for (protocol, fields) in fields.iter().enumerate() {
        let mut bank_fields = Vec::new();
        for (field_index, registers) in fields.iter().enumerate() {
            let width = graph
                .symbol_expr(registers[0])
                .unwrap()
                .get_bv_type(ctx)
                .unwrap();
            let physical = (0..registers.len())
                .map(|bank| {
                    ctx.bv_symbol(
                        &format!("{}$bank{bank}", symbols[registers[0]].full_name(symbols)),
                        width,
                    )
                })
                .collect::<Vec<_>>();
            for (slot, &register) in registers.iter().enumerate() {
                let read = read_bank(ctx, heads[protocol], slot, &physical);
                register_reads.insert(register, read);
                reads.insert(graph.symbol_expr(register).unwrap(), read);
                owners.insert(register, (protocol, field_index, slot));
            }
            bank_fields.push(physical);
        }
        banks.push(bank_fields);
    }

    // lower the nodes. TODO: there is some repeated code here with driver lowering we could resolve.
    let mut bank_next = banks.clone();
    let mut head_next = heads.clone();
    let internal_id = graph.next_node_id().as_u32();
    let node_width = (u32::BITS - internal_id.leading_zeros()).max(1);
    let node_symbol = ctx.bv_symbol("monitor.node", node_width);
    let internal_state = ctx.bit_vec_val(internal_id, node_width);
    let internal_error = ctx.equal(node_symbol, internal_state);
    let bad_id = ctx.bit_vec_val(monitor.bad_state.as_u32(), node_width);
    let bad = ctx.equal(node_symbol, bad_id);
    let mut node_next = internal_state;
    let mut nodes = graph.reachable_node_ids(ctx, graph.entry);
    nodes.sort();
    for node in nodes {
        let node_id = ctx.bit_vec_val(node.as_u32(), node_width);
        let at_node = ctx.equal(node_symbol, node_id);
        for action in &graph[node].actions {
            match &graph[action.op] {
                Op::Assign(register, assignment) => {
                    assert_eq!(action.guard, ctx.get_true());
                    assert_eq!(assignment.dont_care, ctx.get_false());
                    let old = graph.symbol_expr(*register).unwrap();
                    let x = ctx.get_false();
                    let value = assignment.to_expr(ctx, x, old);
                    let value = remap_expr(ctx, value, &reads);
                    let (protocol, field, slot) = owners[register];
                    let count = monitor.control.bank_counts[protocol];
                    for head_value in 0..count {
                        let index =
                            ctx.bit_vec_val(head_value, heads[protocol].get_bv_type(ctx).unwrap());
                        let at_head = ctx.equal(heads[protocol], index);
                        let write = ctx.and(at_node, at_head);
                        let bank = (head_value + slot) % count;
                        bank_next[protocol][field][bank] =
                            ctx.ite(write, value, bank_next[protocol][field][bank]);
                    }
                }
                Op::AssertEq(..) => {
                    panic!("monitor constraints must be lowered into liveness updates")
                }
                Op::Fork | Op::Done | Op::InternalAssertFalse => {}
            }
        }

        // Reverse traversal = first enabled edge priority (though we assume edges are mutex).
        for edge in graph[node].transitions.iter().rev() {
            assert!(edge.consumes_step, "monitor edges must consume one sample");
            let guard = remap_expr(ctx, edge.guard, &reads);
            let taken = ctx.and(at_node, guard);
            let target = ctx.bit_vec_val(edge.target.as_u32(), node_width);
            node_next = ctx.ite(taken, target, node_next);
            for (protocol, proto) in monitor.protocols.iter().enumerate() {
                let amount = edge
                    .rotations
                    .iter()
                    .find(|r| r.protocol == proto.name)
                    .map_or(0, |r| r.amount);
                let next = mod_add(
                    ctx,
                    heads[protocol],
                    amount,
                    monitor.control.bank_counts[protocol],
                );
                head_next[protocol] = ctx.ite(taken, next, head_next[protocol]);
            }
        }
        for action in &graph[node].actions {
            if matches!(graph[action.op], Op::InternalAssertFalse) {
                let guard = remap_expr(ctx, action.guard, &reads);
                let failed = ctx.and(at_node, guard);
                node_next = ctx.ite(failed, internal_state, node_next);
            }
        }
    }

    for (protocol, fields) in fields.iter().enumerate() {
        let zero = ctx.zero(heads[protocol].get_bv_type(ctx).unwrap());
        ts.add_state(
            ctx,
            State {
                symbol: heads[protocol],
                init: Some(zero),
                next: Some(head_next[protocol]),
            },
        );
        for (field, registers) in fields.iter().enumerate() {
            for (bank, &register) in registers.iter().enumerate() {
                ts.add_state(
                    ctx,
                    State {
                        symbol: banks[protocol][field][bank],
                        init: Some(monitor.register_inits[&register]),
                        next: Some(bank_next[protocol][field][bank]),
                    },
                );
            }
        }
    }
    let entry = ctx.bit_vec_val(graph.entry.as_u32(), node_width);
    ts.add_state(
        ctx,
        State {
            symbol: node_symbol,
            init: Some(entry),
            next: Some(node_next),
        },
    );
    ts.bad_states.extend([bad, internal_error]);
    ts.add_output(ctx, Cow::Borrowed("bad"), bad);
    ts.add_output(ctx, Cow::Borrowed("internal_error"), internal_error);
    MonitorTransitionSystemResult {
        ts,
        pin_inputs,
        node_symbol,
        bad,
        internal_error,
        heads,
        register_reads,
    }
}
