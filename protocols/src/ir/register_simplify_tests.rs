use super::*;
use crate::frontend::ast::ProtocolContext;
use crate::frontend::symbol::ROOT_SCOPE;
use crate::ir::proto_graph::{Node, Transition};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::{SymbolValueStore, TypeCheck, eval_expr};

fn fixture(widths: &[u32]) -> (Context, ProtoGraph, SymbolTable, Vec<SymbolId>) {
    let mut ctx = Context::default();
    let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
    let mut symbols = SymbolTable::default();
    let registers = widths
        .iter()
        .enumerate()
        .map(|(index, &width)| {
            let register = graph.add_register(&mut ctx, &mut symbols, &format!("r{index}"), width);
            graph.register_inits.insert(register, ctx.zero(width));
            register
        })
        .collect();
    (ctx, graph, symbols, registers)
}

fn write(ctx: &Context, graph: &mut ProtoGraph, node: NodeId, register: SymbolId, value: ExprRef) {
    let op = graph.o(Op::Assign(
        register,
        Assignment::concrete(ctx.get_false(), ctx.get_true(), value),
    ));
    graph.push_action(node, Action::new(ctx.get_true(), op));
}

fn eval(ctx: &Context, store: &SymbolValueStore, expr: ExprRef) -> BitVecValue {
    eval_expr(ctx, store, expr).try_into().unwrap()
}

// Check the inferred entry facts against simultaneous concrete updates for all
// binary input sequences of four cycles. A sample symbol is reused in the DAG
// but receives a fresh value every cycle, exposing accidental cross-cycle reuse.
fn check_facts(ctx: &Context, graph: &ProtoGraph, analysis: &RegisterAnalysis, inputs: &[ExprRef]) {
    for sequence in 0..(1 << (4 * inputs.len())) {
        let mut state = graph
            .register_inits
            .iter()
            .map(|(&r, &initial)| (r, eval(ctx, &SymbolValueStore::default(), initial)))
            .collect::<FxHashMap<_, _>>();
        let mut node = graph.entry;
        for cycle in 0..4 {
            let mut store = SymbolValueStore::default();
            for (&r, value) in &state {
                let current = graph.symbol_expr(r).unwrap();
                store.define_bv(current, value);
            }
            for (index, &input) in inputs.iter().enumerate() {
                let bit = (sequence >> (cycle * inputs.len() + index)) & 1;
                store.define_bv(
                    input,
                    &BitVecValue::from_u64(bit, input.get_bv_type(ctx).unwrap()),
                );
            }
            for (&r, &fact) in analysis[&node].as_ref().unwrap() {
                assert_eq!(
                    eval(ctx, &store, fact),
                    state[&r],
                    "{node}, {r}, cycle {cycle}, inputs {sequence}"
                );
            }
            let Some(edge) = graph[node]
                .transitions
                .iter()
                .find(|edge| !eval(ctx, &store, edge.guard).is_zero())
            else {
                break;
            };
            let mut next = state.clone();
            for action in &graph[node].actions {
                if eval(ctx, &store, action.guard).is_zero() {
                    continue;
                }
                if let Op::Assign(r, assignment) = graph[action.op].clone() {
                    assert!(eval(ctx, &store, assignment.dont_care).is_zero());
                    if let Some((_, value)) = assignment
                        .concretes
                        .iter()
                        .find(|(guard, _)| !eval(ctx, &store, *guard).is_zero())
                    {
                        next.insert(r, eval(ctx, &store, *value));
                    }
                }
            }
            state = next;
            node = edge.target;
        }
    }
}

#[test]
fn duplicate_capture_uses_stored_value() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 8]);
    let [q, r] = regs[..] else { unreachable!() };
    let data = ctx.bv_symbol("data", 8);
    let q_value = graph.symbol_expr(q).unwrap();
    let r_value = graph.symbol_expr(r).unwrap();
    let a = graph.entry;
    let b = graph.n(Node::empty());
    for register in [q, r] {
        write(&ctx, &mut graph, a, register, data);
    }
    graph.push_transition(a, Transition::new(ctx.get_true(), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
    // Keep a real consumer: r must agree with an independently sampled value.
    let output = ctx.bv_symbol("output", 8);
    let op = graph.o(Op::AssertEq(r_value, output));
    graph.push_action(b, Action::new(ctx.get_true(), op));
    let initial = graph.register_inits.clone();
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &initial);
    assert_eq!(facts[&b].as_ref().unwrap()[&r], q_value);
    check_facts(&ctx, &graph, &facts, &[data]);
    let dead = rewrite_registers(
        &mut ctx,
        &mut graph,
        &symbols,
        a,
        &facts,
        &FxHashSet::default(),
    );
    assert!(dead.contains(&r));
    assert!(!dead.contains(&q));
    assert!(matches!(graph[graph[b].actions[0].op], Op::AssertEq(lhs, _) if lhs == q_value));
}

#[test]
fn reconstructs_address_using_the_updated_counter() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[128, 128]);
    let [index, address] = regs[..] else {
        unreachable!()
    };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let current = graph.symbol_expr(index).unwrap();
    let one = ctx.bit_vec_val(1, 128);
    let next = ctx.add(current, one);
    let base = ctx.bit_vec_val(0x100, 128);
    let two = ctx.bit_vec_val(2, 128);
    let offset = ctx.shift_left(next, two);
    let next_address = ctx.add(base, offset);
    write(&ctx, &mut graph, a, index, next);
    write(&ctx, &mut graph, a, address, next_address);
    graph.push_transition(a, Transition::new(ctx.get_true(), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), a, true));
    let offset = ctx.shift_left(current, two);
    let expected = ctx.add(base, offset);
    let expected = graph.simplifier.simplify(&mut ctx, expected);
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    assert_eq!(facts[&b].as_ref().unwrap()[&address], expected);
    check_facts(&ctx, &graph, &facts, &[]);
}

#[test]
fn conditional_encoding_survives_both_incoming_edges() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[1, 3]);
    let [last, cti] = regs[..] else {
        unreachable!()
    };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let sampled = ctx.bv_symbol("last", 1);
    let seven = ctx.bit_vec_val(7, 3);
    let two = ctx.bit_vec_val(2, 3);
    let encoded = ctx.ite(sampled, seven, two);
    write(&ctx, &mut graph, a, last, sampled);
    write(&ctx, &mut graph, a, cti, encoded);
    graph.push_transition(a, Transition::new(sampled, b, true));
    graph.push_transition(a, Transition::new(ctx.not(sampled), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
    let expected = ctx.ite(graph.symbol_expr(last).unwrap(), seven, two);
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    assert_eq!(facts[&b].as_ref().unwrap().get(&cti), Some(&expected));
    check_facts(&ctx, &graph, &facts, &[sampled]);
}

#[test]
fn priority_and_join_require_the_relationship_on_every_edge() {
    for same in [false, true] {
        let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 8]);
        let [q, r] = regs[..] else { unreachable!() };
        let a = graph.entry;
        let b = graph.n(Node::empty());
        let select = ctx.bv_symbol("select", 1);
        let first = ctx.bv_symbol("first", 8);
        let second = ctx.bv_symbol("second", 8);
        let op = graph.o(Op::Assign(
            q,
            Assignment {
                dont_care: ctx.get_false(),
                // These overlap: the first alternative must win.
                concretes: vec![(select, first), (ctx.get_true(), second)],
            },
        ));
        graph.push_action(a, Action::new(ctx.get_true(), op));
        let value = if same {
            ctx.ite(select, first, second)
        } else {
            first
        };
        write(&ctx, &mut graph, a, r, value);
        graph.push_transition(a, Transition::new(select, b, true));
        graph.push_transition(a, Transition::new(ctx.not(select), b, true));
        graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
        let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
        assert_eq!(
            facts[&b].as_ref().unwrap().get(&r).copied(),
            same.then(|| graph.symbol_expr(q).unwrap())
        );
        check_facts(&ctx, &graph, &facts, &[select, first, second]);
    }
}

#[test]
fn retains_older_capture_when_the_representative_changes() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 8]);
    let [q, r] = regs[..] else { unreachable!() };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let data = ctx.bv_symbol("data", 8);
    for register in [q, r] {
        write(&ctx, &mut graph, a, register, data);
    }
    write(&ctx, &mut graph, b, q, data);
    graph.push_transition(a, Transition::new(ctx.get_true(), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
    let initial = graph.register_inits.clone();
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &initial);
    assert!(!facts[&b].as_ref().unwrap().contains_key(&r));
    check_facts(&ctx, &graph, &facts, &[data]);
}

#[test]
fn simultaneous_swaps_do_not_establish_equality() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 8]);
    let [q, r] = regs[..] else { unreachable!() };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let q_value = graph.symbol_expr(q).unwrap();
    let r_value = graph.symbol_expr(r).unwrap();
    let data = ctx.bv_symbol("data", 8);
    write(&ctx, &mut graph, a, q, data);
    let one = ctx.bit_vec_val(1, 8);
    write(&ctx, &mut graph, a, r, one);
    write(&ctx, &mut graph, b, q, r_value);
    write(&ctx, &mut graph, b, r, q_value);
    graph.push_transition(a, Transition::new(ctx.get_true(), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    assert!(!facts[&b].as_ref().unwrap().contains_key(&r));
    check_facts(&ctx, &graph, &facts, &[data]);
}

#[test]
fn guarded_captures_join_using_shared_facts() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 1, 1, 8]);
    let [data, valid, gate, saved] = regs[..] else {
        unreachable!()
    };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let sample = ctx.bv_symbol("sample", 8);
    let enable = ctx.bv_symbol("enable", 1);
    let gate_sample = ctx.bv_symbol("gate_sample", 1);
    let data_value = graph.symbol_expr(data).unwrap();
    let valid_value = graph.symbol_expr(valid).unwrap();
    let gate_value = graph.symbol_expr(gate).unwrap();
    let saved_value = graph.symbol_expr(saved).unwrap();
    write(&ctx, &mut graph, a, data, sample);
    write(&ctx, &mut graph, a, valid, enable);
    write(&ctx, &mut graph, a, gate, gate_sample);
    let zero = ctx.zero(8);
    let captured = ctx.ite(enable, sample, zero);
    write(&ctx, &mut graph, a, saved, captured);
    graph.push_transition(a, Transition::new(enable, b, true));

    let next = ctx.ite(gate_value, sample, data_value);
    write(&ctx, &mut graph, b, data, next);
    let next = ctx.ite(gate_value, enable, valid_value);
    write(&ctx, &mut graph, b, valid, next);
    write(&ctx, &mut graph, b, gate, gate_sample);
    let enabled = ctx.and(gate_value, enable);
    let next = ctx.ite(enabled, sample, saved_value);
    write(&ctx, &mut graph, b, saved, next);
    graph.push_transition(b, Transition::new(enabled, b, true));

    // Both incoming edges establish valid=1. One represents the saved value
    // through valid; the other selects a branch using the overwritten gate.
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    assert_eq!(facts[&b].as_ref().unwrap().get(&saved), Some(&data_value));
    check_facts(&ctx, &graph, &facts, &[sample, enable, gate_sample]);
}

#[test]
fn incoming_counter_is_not_its_updated_value() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 8]);
    let [index, saved] = regs[..] else {
        unreachable!()
    };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let current = graph.symbol_expr(index).unwrap();
    let one = ctx.bit_vec_val(1, 8);
    let next = ctx.add(current, one);
    write(&ctx, &mut graph, a, index, next);
    write(&ctx, &mut graph, a, saved, current);
    graph.push_transition(a, Transition::new(ctx.get_true(), b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), a, true));
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    assert!(!facts[&b].as_ref().unwrap().contains_key(&saved));
    check_facts(&ctx, &graph, &facts, &[]);
}

#[test]
fn joins_expand_shared_capture_aliases_transitively() {
    let (mut ctx, mut graph, symbols, regs) = fixture(&[8, 1, 1, 1, 8]);
    let [data, valid, first_flag, second_flag, saved] = regs[..] else {
        unreachable!()
    };
    let a = graph.entry;
    let b = graph.n(Node::empty());
    let sample = ctx.bv_symbol("sample", 8);
    let enable = ctx.bv_symbol("enable", 1);
    write(&ctx, &mut graph, a, data, sample);
    write(&ctx, &mut graph, a, valid, enable);
    let flag = ctx.not(enable);
    for r in [first_flag, second_flag] {
        write(&ctx, &mut graph, a, r, flag);
    }
    let zero = ctx.zero(8);
    let captured = ctx.ite(enable, sample, zero);
    write(&ctx, &mut graph, a, saved, captured);
    graph.push_transition(a, Transition::new(enable, b, true));
    graph.push_transition(b, Transition::new(ctx.get_true(), b, true));
    let facts = analyze_registers(&mut ctx, &graph, &symbols, a, &RegisterFacts::default());
    let at_b = facts[&b].as_ref().unwrap();
    assert_eq!(at_b[&first_flag], ctx.get_false());
    assert_eq!(at_b[&second_flag], ctx.get_false());
    assert_eq!(at_b[&saved], graph.symbol_expr(data).unwrap());
    check_facts(&ctx, &graph, &facts, &[sample, enable]);
}
