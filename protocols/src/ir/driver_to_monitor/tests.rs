use super::*;
use baa::{BitVecOps, BitVecValue};
use patronus::expr::eval_bv_expr;

use crate::frontend::ast::ProtocolContext;
use crate::frontend::symbol::{Arg, Dir, Field, ROOT_SCOPE};
use crate::ir::proto_graph::{Node, Transition};

type Values = FxHashMap<ExprRef, BitVecValue>;

/// Keep the caller-owned symbol table alongside the result for test evaluation.
struct TestMonitor {
    ctx: Context,
    automaton: MonitorAutomaton,
    symbols: SymbolTable,
}

impl TestMonitor {
    fn new(mut ctx: Context, graph: ProtoGraph, mut symbols: SymbolTable) -> Self {
        let automaton = convert_driver_to_monitor(&mut ctx, graph, &mut symbols).unwrap();
        Self {
            ctx,
            automaton,
            symbols,
        }
    }

    fn to_dot_string(&self) -> String {
        self.automaton.to_dot_string(&self.ctx, &self.symbols)
    }
}

impl std::ops::Deref for TestMonitor {
    type Target = MonitorAutomaton;

    fn deref(&self) -> &Self::Target {
        &self.automaton
    }
}

struct Fixture {
    ctx: Context,
    graph: ProtoGraph,
    symbols: SymbolTable,
    parameters: Vec<ExprRef>,
    pins: FxHashMap<&'static str, (SymbolId, ExprRef)>,
}

impl Fixture {
    fn new(widths: &[u32], ports: &[(&'static str, Dir, u32)]) -> Self {
        let mut ctx = Context::default();
        let mut symbols = SymbolTable::default();
        let dut_type = symbols.add_struct(
            "Dut".into(),
            ports
                .iter()
                .map(|(name, dir, width)| Field::new((*name).into(), *dir, Type::BitVec(*width)))
                .collect(),
        );
        let dut = symbols.add_without_parent("dut".into(), Type::Struct(dut_type), SymbolKind::Dut);
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        graph.dut_sym = dut;
        let mut parameters = Vec::new();
        for (index, width) in widths.iter().enumerate() {
            let arg = symbols.add_without_parent(
                format!("p{index}"),
                Type::BitVec(*width),
                SymbolKind::Arg(index as u16),
            );
            graph.args.push(Arg::new(arg));
            parameters.push(symbol_expr(&mut ctx, &mut graph, &symbols, arg));
        }
        let pins = ports
            .iter()
            .map(|(name, _, _)| {
                let pin = symbols.add_with_parent((*name).into(), dut);
                (
                    *name,
                    (pin, symbol_expr(&mut ctx, &mut graph, &symbols, pin)),
                )
            })
            .collect();
        Self {
            ctx,
            graph,
            symbols,
            parameters,
            pins,
        }
    }

    fn pin(&self, name: &str) -> ExprRef {
        self.pins[name].1
    }

    fn op(&mut self, node: NodeId, guard: ExprRef, op: Op) {
        let op = self.graph.o(op);
        self.graph.push_action(node, Action::new(guard, op));
    }

    fn check(&mut self, node: NodeId, sample: ExprRef, pattern: ExprRef) {
        self.op(node, self.ctx.get_true(), Op::AssertEq(sample, pattern));
    }

    fn assign(&mut self, node: NodeId, pin: &str, assignment: Assignment) {
        self.op(
            node,
            self.ctx.get_true(),
            Op::Assign(self.pins[pin].0, assignment),
        );
    }

    fn concrete(&mut self, node: NodeId, pin: &str, rhs: ExprRef) {
        self.assign(
            node,
            pin,
            Assignment::concrete(self.ctx.get_false(), self.ctx.get_true(), rhs),
        );
    }

    fn fill_releases(&mut self) {
        let nodes: Vec<_> = self.graph.nodes().map(|(id, _)| id).collect();
        for node in nodes {
            let pins: Vec<_> = self.pins.values().map(|(id, _)| *id).collect();
            for pin in pins {
                if self.symbols[pin].is_in_port()
                    && !self.graph[node]
                        .actions
                        .iter()
                        .any(|a| matches!(self.graph[a.op], Op::Assign(p, _) if p == pin))
                {
                    self.op(
                        node,
                        self.ctx.get_true(),
                        Op::Assign(pin, Assignment::dont_care(self.ctx.get_true())),
                    );
                }
            }
        }
    }

    fn convert(mut self) -> TestMonitor {
        self.fill_releases();
        TestMonitor::new(self.ctx, self.graph, self.symbols)
    }
}

fn initial_values(monitor: &TestMonitor) -> Values {
    let mut values = Values::default();
    for (&register, &init) in &monitor.register_inits {
        values.insert(
            monitor.graph.symbol_expr(register).unwrap(),
            eval_bv_expr(&monitor.ctx, &values, init),
        );
    }
    for pin in monitor.graph.dut_pins(&monitor.symbols) {
        let expr = monitor.graph.symbol_expr(pin).unwrap();
        values.insert(
            expr,
            BitVecValue::zero(expr.get_bv_type(&monitor.ctx).unwrap()),
        );
    }
    values
}

fn set_samples(monitor: &TestMonitor, values: &mut Values, samples: &[(&str, u64)]) {
    for (name, value) in samples {
        let pin = monitor
            .graph
            .dut_pins(&monitor.symbols)
            .find(|pin| monitor.symbols[*pin].name() == *name)
            .unwrap();
        let expr = monitor.graph.symbol_expr(pin).unwrap();
        values.insert(
            expr,
            BitVecValue::from_u64(*value, expr.get_bv_type(&monitor.ctx).unwrap()),
        );
    }
}

#[derive(Debug)]
struct NodeResult {
    consistent: bool,
    internal_error: bool,
    done: bool,
    forks: usize,
}

/// Evaluate only the converted IR, with simultaneous assignments. This is a
/// test helper, not a waveform runner or transition-system backend.
fn evaluate_node(monitor: &TestMonitor, node: NodeId, values: &mut Values) -> NodeResult {
    let graph = &monitor.graph;
    let ctx = &monitor.ctx;
    let eval = |expr| eval_bv_expr(ctx, values, expr);
    let mut updates = Vec::new();
    let mut result = NodeResult {
        consistent: true,
        internal_error: false,
        done: false,
        forks: 0,
    };
    for action in &graph[node].actions {
        if eval(action.guard).is_zero() {
            continue;
        }
        match &graph[action.op] {
            Op::AssertEq(lhs, rhs) => result.consistent &= eval(*lhs) == eval(*rhs),
            Op::Assign(symbol, assignment) => {
                assert_eq!(action.guard, ctx.get_true());
                assert_eq!(assignment.dont_care, ctx.get_false());
                let (_, rhs) = assignment
                    .concretes
                    .iter()
                    .find(|(g, _)| !eval(*g).is_zero())
                    .unwrap();
                updates.push((graph.symbol_expr(*symbol).unwrap(), eval(*rhs)));
            }
            Op::Fork => result.forks += 1,
            Op::Done => result.done = true,
            Op::InternalAssertFalse => result.internal_error = true,
        }
    }
    values.extend(updates);
    result
}

fn binding(monitor: &TestMonitor, values: &Values, index: usize) -> (BitVecValue, BitVecValue) {
    let argument = monitor.graph.args[index].symbol();
    (
        values[&monitor
            .graph
            .symbol_expr(monitor.value_registers[&argument])
            .unwrap()]
            .clone(),
        values[&monitor
            .graph
            .symbol_expr(monitor.knownness_registers[&argument])
            .unwrap()]
            .clone(),
    )
}

fn assert_binding(monitor: &TestMonitor, values: &Values, index: usize, value: u64, mask: u64) {
    let width = monitor.symbols[monitor.graph.args[index].symbol()]
        .tpe()
        .bitwidth();
    assert_eq!(
        binding(monitor, values, index),
        (
            BitVecValue::from_u64(value, width),
            BitVecValue::from_u64(mask, width)
        )
    );
}

#[test]
fn whole_parameter_learning_later_checks_and_metadata() {
    let mut f = Fixture::new(&[8, 7], &[("a", Dir::In, 8), ("b", Dir::Out, 8)]);
    let entry = f.graph.entry;
    let next = f.graph.n(Node::empty());
    f.graph
        .push_transition(entry, Transition::new(f.ctx.get_true(), next, true));
    f.concrete(entry, "a", f.parameters[0]);
    // Parameter operand may be on either side.
    f.check(next, f.parameters[0], f.pin("b"));
    f.op(next, f.ctx.get_true(), Op::Done);
    let original_symbols = f.symbols.clone();
    f.fill_releases();
    let monitor = convert_driver_to_monitor(&mut f.ctx, f.graph, &mut f.symbols).unwrap();
    assert_ne!(f.symbols, original_symbols);
    assert_eq!(f.symbols.get_args(), original_symbols.get_args());
    assert_eq!(monitor.register_inits.len(), 5);
    for (&register, &init) in &monitor.register_inits {
        assert_eq!(f.symbols[register].kind(), SymbolKind::AutomatonState);
        let init = eval_bv_expr(&f.ctx, &Values::default(), init);
        assert_eq!(!init.is_zero(), register == monitor.live_register);
    }
    let monitor = TestMonitor {
        ctx: f.ctx,
        automaton: monitor,
        symbols: f.symbols,
    };
    let mut values = initial_values(&monitor);
    set_samples(&monitor, &mut values, &[("a", 137)]);
    assert!(evaluate_node(&monitor, entry, &mut values).consistent);
    assert_binding(&monitor, &values, 0, 137, 255);
    assert_binding(&monitor, &values, 1, 0, 0);
    let saved = values.clone();
    set_samples(&monitor, &mut values, &[("b", 137)]);
    let result = evaluate_node(&monitor, next, &mut values);
    assert!(result.consistent && result.done && !result.internal_error);
    values = saved;
    set_samples(&monitor, &mut values, &[("b", 136)]);
    let result = evaluate_node(&monitor, next, &mut values);
    assert!(!result.consistent);
    assert!(!result.internal_error);
    assert_binding(&monitor, &values, 0, 137, 255);
    assert!(monitor.to_dot_string().contains("assert_eq"));
}

#[test]
fn conversions_share_the_callers_symbol_table_without_aliasing_registers() {
    let mut f = Fixture::new(&[2], &[]);
    let first = convert_driver_to_monitor(&mut f.ctx, f.graph.clone(), &mut f.symbols).unwrap();
    let second = convert_driver_to_monitor(&mut f.ctx, f.graph, &mut f.symbols).unwrap();
    for register in first.register_inits.keys() {
        assert!(!second.register_inits.contains_key(register));
    }
    let argument = first.graph.args[0].symbol();
    assert_ne!(
        first.value_registers[&argument],
        second.value_registers[&argument]
    );
    assert_ne!(
        first.knownness_registers[&argument],
        second.knownness_registers[&argument]
    );
    for monitor in [&first, &second] {
        for register in monitor.register_inits.keys() {
            let expr = monitor.graph.symbol_expr(*register).unwrap();
            let Expr::BVSymbol { name, .. } = f.ctx[expr] else {
                panic!("register must be a symbol");
            };
            let expected_name = f.symbols[*register].full_name(&f.symbols);
            assert_eq!(&f.ctx[name], expected_name.as_str());
            assert_eq!(
                f.symbols
                    .symbol_id_from_name_in_active_scope(&expected_name),
                Some(*register)
            );
        }
    }
}

#[test]
fn guarded_observations_and_constant_checks() {
    let mut f = Fixture::new(&[4], &[("a", Dir::Out, 4), ("g", Dir::Out, 1)]);
    let entry = f.graph.entry;
    let constant = f.ctx.bit_vec_val(9, 4);
    f.op(entry, f.pin("g"), Op::AssertEq(f.pin("a"), f.parameters[0]));
    f.op(entry, f.pin("g"), Op::AssertEq(f.pin("a"), constant));
    let monitor = f.convert();
    for (g, a, accepted, value, mask) in [
        (0, 3, true, 0, 0),
        (1, 9, true, 9, 15),
        (1, 8, false, 8, 15),
    ] {
        let mut values = initial_values(&monitor);
        set_samples(&monitor, &mut values, &[("a", a), ("g", g)]);
        assert_eq!(
            evaluate_node(&monitor, entry, &mut values).consistent,
            accepted
        );
        assert_binding(&monitor, &values, 0, value, mask);
    }
}

#[test]
fn assignment_alternatives_obey_x_then_first_concrete_priority() {
    let mut f = Fixture::new(
        &[3, 3],
        &[("a", Dir::In, 3), ("g", Dir::Out, 1), ("x", Dir::Out, 1)],
    );
    let entry = f.graph.entry;
    f.assign(
        entry,
        "a",
        Assignment {
            dont_care: f.pin("x"),
            concretes: vec![
                (f.pin("g"), f.parameters[0]),
                (f.ctx.get_true(), f.parameters[1]),
            ],
        },
    );
    let monitor = f.convert();
    for (g, x, masks) in [
        (0, 0, [0, 7]),
        (1, 0, [7, 0]),
        (0, 1, [0, 0]),
        (1, 1, [0, 0]),
    ] {
        let mut values = initial_values(&monitor);
        set_samples(&monitor, &mut values, &[("a", 5), ("g", g), ("x", x)]);
        assert!(evaluate_node(&monitor, entry, &mut values).consistent);
        for (index, mask) in masks.into_iter().enumerate() {
            assert_binding(
                &monitor,
                &values,
                index,
                if mask == 0 { 0 } else { 5 },
                mask,
            );
        }
    }
}

#[test]
fn overlapping_slices_keep_intermediate_checks_and_are_order_independent() {
    let mut f = Fixture::new(&[6], &[("a", Dir::In, 3), ("b", Dir::In, 4)]);
    let entry = f.graph.entry;
    let p = f.parameters[0];
    let a_pattern = f.ctx.slice(p, 3, 1);
    let b_pattern = f.ctx.slice(p, 5, 2);
    f.concrete(entry, "a", a_pattern);
    f.concrete(entry, "b", b_pattern);
    let mut reverse_graph = f.graph.clone();
    reverse_graph.node_mut(entry).actions.reverse();
    let reverse = TestMonitor::new(f.ctx.clone(), reverse_graph, f.symbols.clone());
    let monitor = f.convert();
    for a in 0..8 {
        for b in 0..16 {
            let mut values = initial_values(&monitor);
            let mut rev_values = initial_values(&reverse);
            set_samples(&monitor, &mut values, &[("a", a), ("b", b)]);
            set_samples(&reverse, &mut rev_values, &[("a", a), ("b", b)]);
            let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
            assert_eq!(accepted, (a >> 1) == (b & 3), "a={a}, b={b}");
            assert_eq!(
                accepted,
                evaluate_node(&reverse, entry, &mut rev_values).consistent
            );
            if accepted {
                assert_eq!(
                    binding(&monitor, &values, 0),
                    binding(&reverse, &rev_values, 0)
                );
                assert_binding(&monitor, &values, 0, (a << 1) | (b << 2), 62);
            }
        }
    }
}

#[test]
fn nested_slices_reordered_repeated_parameters_and_constants() {
    let mut f = Fixture::new(&[6, 2], &[("a", Dir::Out, 7), ("b", Dir::Out, 2)]);
    let entry = f.graph.entry;
    let ctx = &mut f.ctx;
    let low = ctx.slice(f.parameters[0], 1, 0);
    let high = ctx.slice(f.parameters[0], 5, 4);
    let constant = ctx.bit_vec_val(1, 1);
    let pattern = ctx.concat(low, constant);
    let pattern = ctx.concat(pattern, high);
    let pattern = ctx.concat(pattern, low);
    let padding = ctx.ones(2);
    let padded = ctx.concat(padding, pattern);
    let inner = ctx.slice(padded, 7, 0);
    let nested = ctx.slice(inner, 6, 0);
    f.check(entry, f.pin("a"), nested);
    f.check(entry, f.pin("b"), f.parameters[1]);
    let monitor = f.convert();
    for a in 0..128 {
        let mut values = initial_values(&monitor);
        set_samples(&monitor, &mut values, &[("a", a), ("b", 3)]);
        let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
        assert_eq!(accepted, (a >> 5) == (a & 3) && ((a >> 4) & 1) == 1);
        if accepted {
            assert_binding(&monitor, &values, 0, (a & 3) | (((a >> 2) & 3) << 4), 51);
            assert_binding(&monitor, &values, 1, 3, 3);
        }
    }
    assert!(monitor.to_dot_string().contains("zero_extend"));
}

#[test]
fn recursive_ites_merge_independent_parameters_and_preserve_inactive_state() {
    let mut f = Fixture::new(
        &[2, 2],
        &[("a", Dir::Out, 2), ("g", Dir::Out, 1), ("h", Dir::Out, 1)],
    );
    let entry = f.graph.entry;
    let constant = f.ctx.bit_vec_val(2, 2);
    let inner = f.ctx.ite(f.pin("h"), f.parameters[0], constant);
    let outer = f.ctx.ite(f.pin("g"), inner, f.parameters[1]);
    f.check(entry, f.pin("a"), outer);
    let monitor = f.convert();
    for g in 0..2 {
        for h in 0..2 {
            for a in 0..4 {
                let mut values = initial_values(&monitor);
                set_samples(&monitor, &mut values, &[("a", a), ("g", g), ("h", h)]);
                let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
                assert_eq!(accepted, g == 0 || h == 1 || a == 2);
                if accepted {
                    assert_binding(
                        &monitor,
                        &values,
                        0,
                        if g == 1 && h == 1 { a } else { 0 },
                        if g == 1 && h == 1 { 3 } else { 0 },
                    );
                    assert_binding(
                        &monitor,
                        &values,
                        1,
                        if g == 0 { a } else { 0 },
                        if g == 0 { 3 } else { 0 },
                    );
                }
            }
        }
    }
    // On a later observation an inactive branch must retain learned bits.
    let mut values = initial_values(&monitor);
    set_samples(&monitor, &mut values, &[("a", 1), ("g", 1), ("h", 1)]);
    assert!(evaluate_node(&monitor, entry, &mut values).consistent);
    set_samples(&monitor, &mut values, &[("a", 3), ("g", 0)]);
    assert!(evaluate_node(&monitor, entry, &mut values).consistent);
    assert_binding(&monitor, &values, 0, 1, 3);
    assert_binding(&monitor, &values, 1, 3, 3);
}

#[test]
fn wide_partial_learning_uses_full_width_masks() {
    let mut f = Fixture::new(&[130], &[("a", Dir::Out, 5), ("b", Dir::Out, 130)]);
    let entry = f.graph.entry;
    let next = f.graph.n(Node::empty());
    f.graph
        .push_transition(entry, Transition::new(f.ctx.get_true(), next, true));
    let top = f.ctx.slice(f.parameters[0], 129, 125);
    f.check(entry, f.pin("a"), top);
    f.check(next, f.pin("b"), f.parameters[0]);
    let monitor = f.convert();
    let mut values = initial_values(&monitor);
    set_samples(&monitor, &mut values, &[("a", 31)]);
    assert!(evaluate_node(&monitor, entry, &mut values).consistent);
    let (value, known) = binding(&monitor, &values, 0);
    let mut ctx = monitor.ctx.clone();
    let ones = ctx.ones(5);
    let extended = ctx.zero_extend(ones, 125);
    let shift = ctx.bit_vec_val(125, 130);
    let top_mask = ctx.shift_left(extended, shift);
    let top_mask = eval_bv_expr(&ctx, &Values::default(), top_mask);
    assert_eq!(value, top_mask);
    assert_eq!(known, top_mask);
    let pin = monitor
        .graph
        .dut_pins(&monitor.symbols)
        .find(|p| monitor.symbols[*p].name() == "b")
        .unwrap();
    let expr = monitor.graph.symbol_expr(pin).unwrap();
    let saved = values.clone();
    values.insert(expr, BitVecValue::ones(130));
    assert!(evaluate_node(&monitor, next, &mut values).consistent);
    assert_eq!(
        binding(&monitor, &values, 0),
        (BitVecValue::ones(130), BitVecValue::ones(130))
    );
    values = saved;
    values.insert(expr, BitVecValue::zero(130));
    assert!(!evaluate_node(&monitor, next, &mut values).consistent);
}

#[test]
fn fork_done_internal_errors_and_control_are_preserved() {
    let mut f = Fixture::new(&[], &[("g", Dir::Out, 1)]);
    let entry = f.graph.entry;
    let next = f.graph.n(Node::empty());
    f.graph
        .push_transition(entry, Transition::new(f.pin("g"), next, true));
    f.op(entry, f.pin("g"), Op::Fork);
    f.op(entry, f.pin("g"), Op::InternalAssertFalse);
    f.op(next, f.ctx.get_true(), Op::Done);
    let monitor = f.convert();
    assert_eq!(monitor.graph.nodes().count(), 2);
    let next = monitor.graph[entry].transitions[0].target;
    let mut values = initial_values(&monitor);
    let result = evaluate_node(&monitor, entry, &mut values);
    assert!(result.consistent && !result.internal_error && result.forks == 0);
    set_samples(&monitor, &mut values, &[("g", 1)]);
    let result = evaluate_node(&monitor, entry, &mut values);
    assert!(result.consistent && result.internal_error && result.forks == 1);
    assert!(evaluate_node(&monitor, next, &mut values).done);
}

/// Independent oracle: assign concrete arguments and check the original driver
/// equalities directly, including assignment priority. It knows nothing about
/// chunks, masks, learning, or the generated monitor expressions.
fn driver_constraints_hold(
    ctx: &Context,
    graph: &ProtoGraph,
    node: NodeId,
    values: &Values,
) -> bool {
    let eval = |expr| eval_bv_expr(ctx, values, expr);
    graph[node].actions.iter().all(|action| {
        if eval(action.guard).is_zero() {
            return true;
        }
        match &graph[action.op] {
            Op::Assign(pin, assignment) => {
                if !eval(assignment.dont_care).is_zero() {
                    return true;
                }
                let (_, rhs) = assignment
                    .concretes
                    .iter()
                    .find(|(g, _)| !eval(*g).is_zero())
                    .unwrap();
                graph.dont_cares.contains(rhs)
                    || eval(graph.symbol_expr(*pin).unwrap()) == eval(*rhs)
            }
            Op::AssertEq(lhs, rhs) => eval(*lhs) == eval(*rhs),
            Op::InternalAssertFalse => false,
            Op::Done | Op::Fork => true,
        }
    })
}

fn filter_candidates(
    ctx: &Context,
    graph: &ProtoGraph,
    node: NodeId,
    samples: &Values,
    candidates: &mut Vec<Vec<u64>>,
) {
    candidates.retain(|candidate| {
        let mut values = samples.clone();
        for (argument, value) in graph.args.iter().zip(candidate) {
            let expr = graph.symbol_expr(argument.symbol()).unwrap();
            values.insert(
                expr,
                BitVecValue::from_u64(*value, expr.get_bv_type(ctx).unwrap()),
            );
        }
        driver_constraints_hold(ctx, graph, node, &values)
    });
}

fn assert_oracle_bindings(monitor: &TestMonitor, values: &Values, candidates: &[Vec<u64>]) {
    assert!(!candidates.is_empty());
    for (index, argument) in monitor.graph.args.iter().enumerate() {
        let mut expected_known = 0;
        let mut expected_value = 0;
        for bit in 0..monitor.symbols[argument.symbol()].tpe().bitwidth() {
            let first = candidates[0][index] & (1 << bit);
            if candidates
                .iter()
                .all(|candidate| candidate[index] & (1 << bit) == first)
            {
                expected_known |= 1 << bit;
                expected_value |= first;
            }
        }
        assert_binding(monitor, values, index, expected_value, expected_known);
    }
}

#[test]
fn exhaustive_equality_oracle_for_concatenations_overlaps_and_independent_ites() {
    let mut f = Fixture::new(
        &[2, 2],
        &[
            ("a", Dir::In, 5),
            ("b", Dir::In, 2),
            ("g", Dir::Out, 1),
            ("h", Dir::Out, 1),
        ],
    );
    let entry = f.graph.entry;
    let first = f.ctx.ite(f.pin("g"), f.parameters[0], f.parameters[1]);
    let constant = f.ctx.one(1);
    let pattern = f.ctx.concat(first, constant);
    let pattern = f.ctx.concat(pattern, f.parameters[0]);
    f.concrete(entry, "a", pattern);
    let constant = f.ctx.bit_vec_val(2, 2);
    let pattern = f.ctx.ite(f.pin("h"), f.parameters[1], constant);
    f.concrete(entry, "b", pattern);
    let driver = f.graph.clone();
    let monitor = f.convert();
    for a in 0..32 {
        for b in 0..4 {
            for g in 0..2 {
                for h in 0..2 {
                    let mut values = initial_values(&monitor);
                    set_samples(
                        &monitor,
                        &mut values,
                        &[("a", a), ("b", b), ("g", g), ("h", h)],
                    );
                    let mut candidates: Vec<_> = (0..4)
                        .flat_map(|p| (0..4).map(move |q| vec![p, q]))
                        .collect();
                    filter_candidates(&monitor.ctx, &driver, entry, &values, &mut candidates);
                    let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
                    assert_eq!(
                        accepted,
                        !candidates.is_empty(),
                        "a={a}, b={b}, g={g}, h={h}"
                    );
                    if accepted {
                        assert_oracle_bindings(&monitor, &values, &candidates);
                    }
                }
            }
        }
    }
}

#[test]
fn exhaustive_equality_oracle_for_nested_slices_trimming_chunks() {
    for (hi, lo) in [(7, 0), (7, 1), (6, 1), (5, 3)] {
        let width = hi - lo + 1;
        let mut f = Fixture::new(&[3, 2], &[("a", Dir::Out, width)]);
        let entry = f.graph.entry;
        let ctx = &mut f.ctx;
        let constant = ctx.bit_vec_val(2, 2);
        let repeated = ctx.slice(f.parameters[0], 2, 1);
        let pattern = ctx.concat(f.parameters[0], constant);
        let pattern = ctx.concat(pattern, f.parameters[1]);
        let pattern = ctx.concat(pattern, repeated);
        // Two actual slices, with the outer one trimming parameter and constant
        // chunks at different boundaries for each range.
        let inner = ctx.slice(pattern, 7, 0);
        let sliced = ctx.slice(inner, hi, lo);
        f.check(entry, f.pin("a"), sliced);
        let driver = f.graph.clone();
        let monitor = f.convert();
        for a in 0..(1 << width) {
            let mut values = initial_values(&monitor);
            set_samples(&monitor, &mut values, &[("a", a)]);
            let mut candidates: Vec<_> = (0..8)
                .flat_map(|p| (0..4).map(move |q| vec![p, q]))
                .collect();
            filter_candidates(&monitor.ctx, &driver, entry, &values, &mut candidates);
            let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
            assert_eq!(accepted, !candidates.is_empty(), "range={hi}:{lo}, a={a}");
            if accepted {
                assert_oracle_bindings(&monitor, &values, &candidates);
            }
        }
    }
}

#[test]
fn parameter_free_equalities_stay_checks_and_sampled_arithmetic_can_bind() {
    let mut f = Fixture::new(
        &[4],
        &[("a", Dir::Out, 4), ("b", Dir::Out, 4), ("c", Dir::Out, 4)],
    );
    let entry = f.graph.entry;
    let sum = f.ctx.add(f.pin("a"), f.pin("b"));
    f.check(entry, f.parameters[0], sum);
    f.check(entry, sum, f.pin("c"));
    let c = f.pin("c");
    let monitor = f.convert();
    assert!(monitor.graph[entry].actions.iter().any(|a| {
        matches!(monitor.graph[a.op], Op::AssertEq(lhs, rhs) if lhs == sum && rhs == c)
    }));
    for (a, b, c, accepted) in [(2, 3, 5, true), (2, 3, 4, false), (15, 2, 1, true)] {
        let mut values = initial_values(&monitor);
        set_samples(&monitor, &mut values, &[("a", a), ("b", b), ("c", c)]);
        assert_eq!(
            evaluate_node(&monitor, entry, &mut values).consistent,
            accepted
        );
        if accepted {
            assert_binding(&monitor, &values, 0, c, 15);
        }
    }
}

#[test]
fn independent_ites_do_not_enumerate_combinations_across_observations() {
    let names = ["a", "b", "c", "d", "e", "f", "i", "j", "k", "l", "m", "n"];
    let mut ports: Vec<_> = names.iter().map(|name| (*name, Dir::Out, 1)).collect();
    ports.push(("g", Dir::Out, 1));
    let mut f = Fixture::new(&[1, 1], &ports);
    let entry = f.graph.entry;
    let pattern = f.ctx.ite(f.pin("g"), f.parameters[0], f.parameters[1]);
    for name in names {
        f.check(entry, f.pin(name), pattern);
    }
    let monitor = f.convert();
    let actions = &monitor.graph[entry].actions;
    assert_eq!(
        actions
            .iter()
            .filter(|a| matches!(monitor.graph[a.op], Op::AssertEq(_, _)))
            .count(),
        24
    );
    assert_eq!(
        actions
            .iter()
            .filter(|a| matches!(monitor.graph[a.op], Op::Assign(_, _)))
            .count(),
        4
    );
}

#[test]
fn loop_first_observation_learns_and_subsequent_observations_check() {
    let mut f = Fixture::new(&[2], &[("a", Dir::Out, 2)]);
    let entry = f.graph.entry;
    f.graph
        .push_transition(entry, Transition::new(f.ctx.get_true(), entry, true));
    f.check(entry, f.pin("a"), f.parameters[0]);
    let driver = f.graph.clone();
    let monitor = f.convert();
    for first in 0..4 {
        for second in 0..4 {
            let mut values = initial_values(&monitor);
            let mut candidates: Vec<_> = (0..4).map(|p| vec![p]).collect();
            for a in [first, second] {
                set_samples(&monitor, &mut values, &[("a", a)]);
                filter_candidates(&monitor.ctx, &driver, entry, &values, &mut candidates);
                assert_eq!(
                    evaluate_node(&monitor, entry, &mut values).consistent,
                    !candidates.is_empty()
                );
                if !candidates.is_empty() {
                    assert_oracle_bindings(&monitor, &values, &candidates);
                }
            }
        }
    }
}

fn prepare_source(source: &str) -> (Context, ProtoGraph, SymbolTable) {
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::edge_contract::contract_edges;
    use crate::ir::lowering::lower_ast_to_ir;
    use crate::ir::propagate_assigns::propagate_assignments;
    use crate::ir::reaching_defs::reaching_definitions;

    let file = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(file.path(), source).unwrap();
    let mut handler = DiagnosticHandler::default();
    let (symbols, modules) = frontend(&[file.path()], &mut handler, true, false).unwrap();
    let module = require_single_module(modules, &[file.path()]).unwrap();
    let mut ctx = Context::default();
    let mut graph = lower_ast_to_ir(
        &mut ctx,
        module.protos.into_iter().next().unwrap(),
        &symbols,
    );
    contract_edges(&mut ctx, &mut graph, &symbols);
    let rd = reaching_definitions(&mut ctx, &mut graph, &symbols);
    propagate_assignments(&mut ctx, &mut graph, &symbols, &rd);
    graph.simplify_all_exprs(&mut ctx);
    graph.garbage_collect_unreachable(&ctx);
    (ctx, graph, symbols)
}

/// Set PROTOCOLS_MONITOR_DOT to export a standalone DOT file from this test.
#[test]
fn overlapping_slices_dot_snapshot() {
    let (ctx, driver, symbols) = prepare_source(include_str!("fixtures/overlapping_slices.prot"));
    let monitor = TestMonitor::new(ctx, driver, symbols);
    let dot = monitor.to_dot_string();
    if let Some(path) = std::env::var_os("PROTOCOLS_MONITOR_DOT") {
        let path = std::path::PathBuf::from(path);
        std::fs::write(&path, &dot).unwrap();
        println!("Monitor DOT written to {}", path.display());
    }
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path("../../tests/snapshots");
    settings.bind(|| {
        insta::assert_snapshot!("overlapping_slices_monitor", dot);
    });

    let entry = monitor.graph.entry;
    for a in 0..8 {
        for b in 0..8 {
            let mut values = initial_values(&monitor);
            set_samples(&monitor, &mut values, &[("a", a), ("b", b)]);
            let accepted = evaluate_node(&monitor, entry, &mut values).consistent;
            assert_eq!(accepted, a >> 1 == b & 3, "a={a}, b={b}");
            if accepted {
                assert_binding(&monitor, &values, 0, (a << 1) | (b << 2), 30);
            }
        }
    }
}

#[test]
fn prepared_driver_overwrites_persists_and_releases_assignments() {
    let (ctx, driver, symbols) = prepare_source(
        r#"
        struct Dut { in a: u4, out b: u4, }
        prot test<dut: Dut>(p: u4, unused: u4) {
            dut.a := unused;
            dut.a := p;
            step();
            step();
            dut.a := X;
            assert_eq(p, dut.b);
            step();
        }
    "#,
    );
    let monitor = TestMonitor::new(ctx, driver, symbols);
    let mut values = initial_values(&monitor);
    let mut node = monitor.graph.entry;
    set_samples(&monitor, &mut values, &[("a", 6)]);
    assert!(evaluate_node(&monitor, node, &mut values).consistent);
    assert_binding(&monitor, &values, 0, 6, 15);
    assert_binding(&monitor, &values, 1, 0, 0);
    node = monitor.graph[node].transitions[0].target;
    let saved = values.clone();
    set_samples(&monitor, &mut values, &[("a", 7)]);
    assert!(!evaluate_node(&monitor, node, &mut values).consistent);
    values = saved;
    set_samples(&monitor, &mut values, &[("a", 6)]);
    assert!(evaluate_node(&monitor, node, &mut values).consistent);
    node = monitor.graph[node].transitions[0].target;
    set_samples(&monitor, &mut values, &[("a", 13), ("b", 6)]);
    assert!(evaluate_node(&monitor, node, &mut values).consistent);
    node = monitor.graph[node].transitions[0].target;
    let result = evaluate_node(&monitor, node, &mut values);
    assert!(result.done && result.consistent);
}

#[test]
fn prepared_driver_branch_join_learns_only_on_the_active_path() {
    let (ctx, driver, symbols) = prepare_source(
        r#"
        struct Dut { in a: u2, out g: u1, out b: u2, }
        prot test<dut: Dut>(p: u2) {
            if dut.g { dut.a := p; }
            step();
            dut.a := X;
            assert_eq(p, dut.b);
            step();
        }
    "#,
    );
    let monitor = TestMonitor::new(ctx, driver, symbols);
    let entry = monitor.graph.entry;
    for g in 0..2 {
        for b in 0..4 {
            let mut values = initial_values(&monitor);
            set_samples(&monitor, &mut values, &[("a", 1), ("g", g)]);
            assert!(evaluate_node(&monitor, entry, &mut values).consistent);
            assert_binding(
                &monitor,
                &values,
                0,
                if g == 1 { 1 } else { 0 },
                if g == 1 { 3 } else { 0 },
            );
            let next = monitor.graph[entry]
                .transitions
                .iter()
                .find(|t| !eval_bv_expr(&monitor.ctx, &values, t.guard).is_zero())
                .unwrap()
                .target;
            set_samples(&monitor, &mut values, &[("a", 3), ("b", b)]);
            assert_eq!(
                evaluate_node(&monitor, next, &mut values).consistent,
                g == 0 || b == 1
            );
            if g == 0 || b == 1 {
                assert_binding(&monitor, &values, 0, b, 3);
            }
        }
    }
}

fn error_text(mut f: Fixture) -> String {
    match convert_driver_to_monitor(&mut f.ctx, f.graph, &mut f.symbols) {
        Ok(_) => panic!("expected a conversion error"),
        Err(error) => error.to_string(),
    }
}

#[test]
fn unsupported_parameter_expressions_have_descriptive_errors() {
    let mut f = Fixture::new(&[2], &[("a", Dir::Out, 2)]);
    let one = f.ctx.one(2);
    let arithmetic = f.ctx.add(f.parameters[0], one);
    f.check(f.graph.entry, f.pin("a"), arithmetic);
    assert!(error_text(f).contains("parameter arithmetic"));

    let mut f = Fixture::new(&[2, 2], &[]);
    f.check(f.graph.entry, f.parameters[0], f.parameters[1]);
    assert!(error_text(f).contains("relations between unresolved parameters"));

    let mut f = Fixture::new(&[], &[]);
    let seq = f.symbols.add_seq(Type::BitVec(2), 1);
    let arg = f
        .symbols
        .add_without_parent("seq_arg".into(), Type::Seq(seq), SymbolKind::Arg(0));
    f.graph.args.push(Arg::new(arg));
    let error = error_text(f);
    assert!(error.contains("scalar bit vector") && error.contains("seq_arg"));
}

#[test]
fn parameter_dependent_guards_and_ite_conditions_are_rejected() {
    let mut f = Fixture::new(&[1], &[("a", Dir::Out, 1)]);
    f.op(
        f.graph.entry,
        f.parameters[0],
        Op::AssertEq(f.pin("a"), f.ctx.get_true()),
    );
    assert!(error_text(f).contains("parameter-dependent action guard"));

    let mut f = Fixture::new(&[1], &[]);
    let entry = f.graph.entry;
    f.graph
        .push_transition(entry, Transition::new(f.parameters[0], entry, true));
    assert!(error_text(f).contains("parameter-dependent transition guard"));

    let mut f = Fixture::new(&[1, 2], &[("a", Dir::Out, 2)]);
    let constant = f.ctx.zero(2);
    let ite = f.ctx.ite(f.parameters[0], f.parameters[1], constant);
    f.check(f.graph.entry, f.pin("a"), ite);
    assert!(error_text(f).contains("parameter-dependent ITE condition"));

    let mut f = Fixture::new(&[1, 2], &[("a", Dir::In, 2)]);
    f.assign(
        f.graph.entry,
        "a",
        Assignment {
            dont_care: f.parameters[0],
            concretes: vec![(f.ctx.get_true(), f.parameters[1])],
        },
    );
    assert!(error_text(f).contains("parameter-dependent assignment guard"));
}

#[test]
fn unprepared_graphs_are_rejected_instead_of_dropping_constraints() {
    let mut f = Fixture::new(&[2], &[("a", Dir::In, 2), ("g", Dir::Out, 1)]);
    f.assign(
        f.graph.entry,
        "a",
        Assignment::concrete(f.ctx.get_false(), f.pin("g"), f.parameters[0]),
    );
    assert!(error_text(f).contains("not total"));

    let f = Fixture::new(&[], &[("a", Dir::In, 2)]);
    assert!(error_text(f).contains("missing effective assignments"));

    let mut f = Fixture::new(&[2], &[("a", Dir::In, 2)]);
    f.concrete(f.graph.entry, "a", f.parameters[0]);
    f.concrete(f.graph.entry, "a", f.parameters[0]);
    assert!(error_text(f).contains("one effective assignment"));

    let mut f = Fixture::new(&[], &[]);
    let next = f.graph.n(Node::empty());
    f.graph.push_transition(
        f.graph.entry,
        Transition::new(f.ctx.get_true(), next, false),
    );
    assert!(error_text(f).contains("contracted single-protocol"));
}
