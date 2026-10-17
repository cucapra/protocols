use super::*;
use crate::frontend;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::require_single_module;
use crate::ir::joint_automaton::build_joint_driver_automaton;

fn selected(filename: &str, names: &[&str]) -> (Vec<Protocol>, SymbolTable) {
    let mut handler = DiagnosticHandler::default();
    let (symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
    let module = require_single_module(modules, &[filename]).unwrap();
    let protocols = module
        .protos
        .into_iter()
        .filter(|p| names.contains(&p.name.as_str()))
        .collect();
    (protocols, symbols)
}

#[test]
fn pipelined_monitors_share_the_driver_control_shape() {
    for (filename, names, banks) in [
        ("../tests/adders/adder_d1/add_d1.prot", vec!["add"], vec![2]),
        ("../tests/adders/adder_d2/add_d2.prot", vec!["add"], vec![3]),
        (
            "../tests/meta/unbounded_pre_phase_steady_state_simple.prot",
            vec!["id", "w"],
            vec![],
        ),
        (
            "../tests/alus/alu_d1.prot",
            vec!["add", "sub", "and", "or"],
            vec![],
        ),
        (
            "../tests/alus/alu_d2.prot",
            vec!["add", "sub", "and", "or"],
            vec![],
        ),
    ] {
        let (protocols, mut symbols) = selected(filename, &names);
        let mut ctx = Context::default();
        let driver = build_joint_driver_automaton(&mut ctx, protocols.clone(), &symbols).unwrap();
        let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
        if !banks.is_empty() {
            assert_eq!(monitor.control.bank_counts, banks);
        }
        assert_eq!(monitor.control.bank_counts, driver.bank_counts);
        assert_eq!(monitor.control.choice_slots, driver.choice_slots);
        assert_eq!(monitor.control.graph.entry, driver.graph.entry);
        assert_eq!(
            monitor.control.graph.nodes().count(),
            driver.graph.nodes().count() + 1
        );
        for (_, data) in driver.graph.nodes() {
            for input in driver.graph.dut_input_symbols(&symbols) {
                assert_eq!(data.actions.iter().filter(|action| {
                    matches!(driver.graph[action.op], Op::Assign(target, _) if target == input)
                }).count(), 1, "each shared DUT input needs one effective assignment");
            }
        }
        for (node, data) in monitor.control.graph.nodes() {
            if node == monitor.bad_state {
                continue;
            }
            assert_eq!(
                data.transitions.len(),
                driver.graph[node].transitions.len() + 1
            );
            assert_eq!(data.transitions.last().unwrap().target, monitor.bad_state);
            for (monitor_edge, driver_edge) in
                data.transitions.iter().zip(&driver.graph[node].transitions)
            {
                assert_eq!(monitor_edge.target, driver_edge.target);
                assert_eq!(monitor_edge.rotations, driver_edge.rotations);
            }
            for (index, action) in data.actions.iter().enumerate() {
                match &monitor.control.graph[action.op] {
                    Op::Assign(register, _) => {
                        assert!(monitor.register_inits.contains_key(register));
                        assert_eq!(action.guard, ctx.get_true());
                        assert!(monitor.action_owners.contains_key(&(node, index)));
                    }
                    Op::Done => assert!(!monitor.action_owners.contains_key(&(node, index))),
                    _ => assert!(monitor.action_owners.contains_key(&(node, index))),
                }
            }
        }
    }
}

use baa::{BitVecOps, BitVecValue};
use patronus::expr::{eval_bv_expr, find_symbols};

fn from_source(source: &str) -> (Vec<Protocol>, SymbolTable) {
    let file = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(file.path(), source).unwrap();
    let mut handler = DiagnosticHandler::default();
    let (symbols, modules) = frontend(&[file.path()], &mut handler, true, false).unwrap();
    let module = require_single_module(modules, &[file.path()]).unwrap();
    (module.protos, symbols)
}

struct Execution {
    node: NodeId,
    values: FxHashMap<ExprRef, BitVecValue>,
}

impl Execution {
    fn new(ctx: &Context, monitor: &JointMonitorAutomaton) -> Self {
        let mut values = FxHashMap::default();
        for (&register, &init) in &monitor.register_inits {
            values.insert(
                monitor.control.graph.symbol_expr(register).unwrap(),
                eval_bv_expr(ctx, &FxHashMap::default(), init),
            );
        }
        Self {
            node: monitor.control.graph.entry,
            values,
        }
    }

    fn sample(
        &mut self,
        ctx: &Context,
        monitor: &JointMonitorAutomaton,
        symbols: &SymbolTable,
        sample: &[(&str, u64)],
    ) -> bool {
        let control = &monitor.control;
        let graph = &control.graph;
        for pin in graph.dut_pins(symbols) {
            let expr = graph.symbol_expr(pin).unwrap();
            let value = sample
                .iter()
                .find(|(name, _)| *name == symbols[pin].name())
                .map_or(0, |(_, value)| *value);
            self.values.insert(
                expr,
                BitVecValue::from_u64(value, expr.get_bv_type(ctx).unwrap()),
            );
        }
        let eval = |expr| eval_bv_expr(ctx, &self.values, expr);
        let mut updates = Vec::new();
        for action in &graph[self.node].actions {
            if eval(action.guard).is_zero() {
                continue;
            }
            match &graph[action.op] {
                Op::AssertEq(..) => panic!("constraints must be lowered before composition"),
                Op::InternalAssertFalse => {
                    panic!("internal errors must remain separate from mismatches")
                }
                Op::Assign(register, assignment) => {
                    assert!(eval(assignment.dont_care).is_zero());
                    if let Some(&(_, rhs)) = assignment
                        .concretes
                        .iter()
                        .find(|(guard, _)| !eval(*guard).is_zero())
                    {
                        updates.push((graph.symbol_expr(*register).unwrap(), eval(rhs)));
                    }
                }
                Op::Done => {}
                _ => {}
            }
        }
        // All right-hand sides above read the incoming state. Apply their
        // results together before evaluating edges against the updated state.
        self.values.extend(updates);
        let eval = |expr| eval_bv_expr(ctx, &self.values, expr);
        let transitions = graph[self.node]
            .transitions
            .iter()
            .filter(|edge| !eval(edge.guard).is_zero())
            .collect::<Vec<_>>();
        // Uniqueness is an assumption, so the interpreter does not check it.
        // Tests involving ambiguity inspect all enabled edges separately.
        let edge = transitions.first().copied();
        let Some(edge) = edge else {
            return false;
        };
        // The automata describe logical FIFO slots. Interpret their existing
        // rotation annotations directly, without constructing a transition system.
        let before = self.values.clone();
        for rotation in &edge.rotations {
            let protocol = monitor
                .protocols
                .iter()
                .position(|p| p.name == rotation.protocol)
                .unwrap();
            for slot in 0..control.bank_counts[protocol] - rotation.amount {
                for registers in [&monitor.value_registers, &monitor.knownness_registers] {
                    for (key, &target) in registers {
                        if key.0 == protocol && key.1 == slot {
                            let source = registers[&(protocol, slot + rotation.amount, key.2)];
                            let target = graph.symbol_expr(target).unwrap();
                            let source = graph.symbol_expr(source).unwrap();
                            self.values.insert(target, before[&source].clone());
                        }
                    }
                }
                let target = graph
                    .symbol_expr(monitor.live_registers[&(protocol, slot)])
                    .unwrap();
                let source = graph
                    .symbol_expr(monitor.live_registers[&(protocol, slot + rotation.amount)])
                    .unwrap();
                self.values.insert(target, before[&source].clone());
            }
        }
        self.node = edge.target;
        self.node != monitor.bad_state
    }

    fn can_finish(&self, ctx: &Context, monitor: &JointMonitorAutomaton) -> bool {
        let values = &self.values;
        monitor.control.graph[self.node]
            .actions
            .iter()
            .any(|action| {
                matches!(monitor.control.graph[action.op], Op::Done)
                    && !eval_bv_expr(ctx, values, action.guard).is_zero()
            })
    }
}

const PARTIAL_PIPELINE: &str = r#"
struct Dut { out start: u1, out g: u1, out a: u1, out b: u1, out c: u2, }
prot partial<DUT: Dut>(p: u2) {
    assert_eq(DUT.start, 1'b1);
    if DUT.g { assert_eq(p[0], DUT.a); }
    step();
    fork();
    assert_eq(p[1], DUT.b);
    step();
    assert_eq(p, DUT.c);
    step();
}
prot idle<DUT: Dut>() { assert_eq(DUT.start, 1'b0); step(); }
"#;

#[test]
fn reused_slots_reset_partial_bindings_and_preserve_overlapping_transactions() {
    let (protocols, mut symbols) = from_source(PARTIAL_PIPELINE);
    let mut ctx = Context::default();
    let sources = prepare_joint_protocols(&mut ctx, &protocols, &symbols).unwrap();
    let naive = sources
        .into_iter()
        .map(|graph| convert_driver_to_monitor(&mut ctx, graph, &mut symbols).unwrap())
        .collect();
    let naive =
        compose_joint_monitor_automaton(&mut ctx, protocols.clone(), naive, &mut symbols).unwrap();
    let optimized = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    assert_eq!(optimized.control.bank_counts, vec![3, 1]);
    let transactions = [
        (true, 3),
        (false, 0),
        (true, 0),
        (false, 3),
        (true, 1),
        (false, 2),
        (true, 2),
        (false, 1),
    ];
    let samples = (0..transactions.len() + 2)
        .map(|cycle| {
            let (g, value) = transactions.get(cycle).copied().unwrap_or((false, 0));
            let b = cycle
                .checked_sub(1)
                .and_then(|i| transactions.get(i))
                .map_or(0, |(_, value)| value >> 1);
            let c = cycle
                .checked_sub(2)
                .and_then(|i| transactions.get(i))
                .map_or(0, |(_, value)| *value);
            vec![
                ("g", u64::from(g)),
                ("a", value & 1),
                ("b", b),
                ("c", c),
                ("start", u64::from(cycle < transactions.len())),
            ]
        })
        .collect::<Vec<_>>();
    let run = |monitor: &JointMonitorAutomaton, mutation: Option<(usize, usize, u64)>| {
        let mut execution = Execution::new(&ctx, monitor);
        for (cycle, inputs) in samples.iter().enumerate() {
            let mut inputs = inputs.clone();
            if let Some((at, pin, mask)) = mutation
                && cycle == at
            {
                inputs[pin].1 ^= mask;
            }
            if !execution.sample(&ctx, monitor, &symbols, &inputs) {
                return false;
            }
        }
        assert!(execution.can_finish(&ctx, monitor));
        true
    };
    let mut naive_execution = Execution::new(&ctx, &naive);
    let mut optimized_execution = Execution::new(&ctx, &optimized);
    for (cycle, inputs) in samples.iter().enumerate() {
        assert!(naive_execution.sample(&ctx, &naive, &symbols, inputs));
        assert!(optimized_execution.sample(&ctx, &optimized, &symbols, inputs));
        assert_eq!(naive_execution.node, optimized_execution.node);
        for (key, &expression) in &naive.knownness_outputs[&naive_execution.node] {
            let known = eval_bv_expr(&ctx, &naive_execution.values, expression);
            let optimized_known = eval_bv_expr(
                &ctx,
                &optimized_execution.values,
                optimized.knownness_outputs[&optimized_execution.node][key],
            );
            assert_eq!(known, optimized_known, "mask at cycle {cycle}");
            let value = &naive_execution.values[&naive
                .control
                .graph
                .symbol_expr(naive.value_registers[key])
                .unwrap()];
            let optimized_value = &optimized_execution.values[&optimized
                .control
                .graph
                .symbol_expr(optimized.value_registers[key])
                .unwrap()];
            assert_eq!(
                value.and(&known),
                optimized_value.and(&optimized_known),
                "learned bits at cycle {cycle}"
            );
        }
    }
    assert!(run(&naive, None));
    assert!(run(&optimized, None));
    // Both bit observations must match the later whole value. When g is false,
    // the first bit has no earlier constraint and remains freely learnable.
    for (transaction, &(g, _)) in transactions.iter().enumerate() {
        for bit in 0..2 {
            let mutation = Some((transaction + 2, 3, 1 << bit));
            let expected = bit == 0 && !g;
            assert_eq!(
                run(&naive, mutation),
                expected,
                "naive: transaction={transaction}, bit={bit}"
            );
            assert_eq!(
                run(&optimized, mutation),
                expected,
                "optimized: transaction={transaction}, bit={bit}"
            );
        }
    }
}

#[test]
fn every_instance_remaps_reads_and_assignment_targets_together() {
    let (protocols, mut symbols) = from_source(PARTIAL_PIPELINE);
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let graph = &monitor.control.graph;
    let sampled = graph
        .dut_pins(&symbols)
        .map(|pin| graph.symbol_expr(pin).unwrap())
        .collect::<FxHashSet<_>>();
    for (node, data) in graph.nodes() {
        for (index, action) in data.actions.iter().enumerate() {
            let Some(&owner) = monitor.action_owners.get(&(node, index)) else {
                continue;
            };
            let owned = monitor
                .value_registers
                .iter()
                .chain(&monitor.knownness_registers)
                .filter(|(key, _)| (key.0, key.1) == owner)
                .map(|(_, register)| graph.symbol_expr(*register).unwrap())
                .chain([graph.symbol_expr(monitor.live_registers[&owner]).unwrap()])
                .collect::<FxHashSet<_>>();
            let mut roots = vec![action.guard];
            match &graph[action.op] {
                Op::Assign(register, assignment) => {
                    assert!(owned.contains(&graph.symbol_expr(*register).unwrap()));
                    roots.push(assignment.dont_care);
                    roots.extend(
                        assignment
                            .concretes
                            .iter()
                            .flat_map(|&(guard, rhs)| [guard, rhs]),
                    );
                }
                Op::AssertEq(a, b) => roots.extend([*a, *b]),
                _ => {}
            }
            for root in roots {
                for symbol in find_symbols(&ctx, root) {
                    assert!(
                        sampled.contains(&symbol) || owned.contains(&symbol),
                        "unmapped or foreign register in instance {owner:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn launch_selection_and_overlapping_protocols_keep_constraints_separate() {
    let (protocols, mut symbols) = from_source(
        r#"
        struct Dut { out start: u1, in tag: u1, in a: u2, out b: u2, }
        prot zero<DUT: Dut>(p: u2) {
            assert_eq(DUT.start, 1'b1);
            DUT.tag := 1'b0; DUT.a := p; step();
            DUT.tag := X; DUT.a := X; fork(); assert_eq(p, DUT.b); step();
        }
        prot one<DUT: Dut>(p: u2) {
            assert_eq(DUT.start, 1'b1);
            DUT.tag := 1'b1; DUT.a := p; step();
            DUT.tag := X; DUT.a := X; fork(); assert_eq(p, DUT.b); step();
        }
        prot idle<DUT: Dut>() { assert_eq(DUT.start, 1'b0); step(); }
    "#,
    );
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let mut execution = Execution::new(&ctx, &monitor);
    for cycle in 0..20 {
        let choice = cycle % 2;
        let value = (cycle * 3) % 4;
        let previous = if cycle == 0 { 0 } else { ((cycle - 1) * 3) % 4 };
        assert!(execution.sample(
            &ctx,
            &monitor,
            &symbols,
            &[
                ("start", 1),
                ("tag", choice as u64),
                ("a", value as u64),
                ("b", previous as u64)
            ]
        ));
    }
    assert!(execution.sample(&ctx, &monitor, &symbols, &[("b", 1)]));
    assert!(execution.can_finish(&ctx, &monitor));
    // The sampled tag selects protocol one; no external choice is supplied.
    let mut selected_by_sample = Execution::new(&ctx, &monitor);
    assert!(selected_by_sample.sample(&ctx, &monitor, &symbols, &[("start", 1), ("tag", 1)]));
    for protocol in 0..2 {
        let live = monitor
            .control
            .graph
            .symbol_expr(monitor.live_registers[&(protocol, 0)])
            .unwrap();
        assert_eq!(
            selected_by_sample.values[&live].to_bool(),
            Some(protocol == 1)
        );
    }
    let mut wrong_output = Execution::new(&ctx, &monitor);
    assert!(wrong_output.sample(
        &ctx,
        &monitor,
        &symbols,
        &[("start", 1), ("tag", 1), ("a", 3)]
    ));
    assert!(!wrong_output.sample(&ctx, &monitor, &symbols, &[("b", 2)]));
}

#[test]
fn pre_phase_can_wait_for_arbitrarily_many_samples() {
    let (protocols, mut symbols) = from_source(
        r#"
        struct Dut { out start: u1, out a: u2, out b: u2, out ready: u1, }
        prot wait<DUT: Dut>(p: u2) {
            assert_eq(DUT.start, 1'b1);
            assert_eq(p, DUT.a); step();
            while !DUT.ready { assert_eq(p, DUT.a); step(); }
            step();
            fork(); assert_eq(p, DUT.b); step();
        }
        prot idle<DUT: Dut>() { assert_eq(DUT.start, 1'b0); step(); }
    "#,
    );
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    for cycles in [0, 1, 25] {
        let mut execution = Execution::new(&ctx, &monitor);
        assert!(execution.can_finish(&ctx, &monitor)); // Empty interpretation.
        assert!(execution.sample(&ctx, &monitor, &symbols, &[("start", 1), ("a", 2)]));
        assert!(!execution.can_finish(&ctx, &monitor));
        for _ in 0..cycles {
            assert!(execution.sample(&ctx, &monitor, &symbols, &[("a", 2)]));
        }
        assert!(execution.sample(&ctx, &monitor, &symbols, &[("ready", 1)]));
        assert!(execution.sample(&ctx, &monitor, &symbols, &[("b", 2)]));
        assert!(execution.can_finish(&ctx, &monitor));
    }
}

#[test]
fn unsupported_parameter_arithmetic_reports_the_protocol() {
    let (protocols, mut symbols) = from_source(
        r#"
        struct Dut { in a: u2, }
        prot arithmetic<DUT: Dut>(p: u2) { DUT.a := p + 2'd1; step(); }
    "#,
    );
    let mut ctx = Context::default();
    let error = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols)
        .err()
        .unwrap()
        .to_string();
    assert!(error.contains("arithmetic"));
    assert!(error.contains("unsupported monitor expression"));
    assert!(matches!(
        build_joint_monitor_automaton(&mut ctx, vec![], &mut symbols),
        Err(JointMonitorError::Control(
            JointAutomatonError::EmptyProtocolSet
        ))
    ));
}

#[test]
fn four_protocols_are_selected_by_the_current_sample() {
    let (protocols, mut symbols) =
        selected("../tests/alus/alu_d1.prot", &["add", "sub", "and", "or"]);
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let graph = &monitor.control.graph;
    let dot = monitor.to_dot_string(&ctx, &symbols);
    assert!(!dot.contains("protocol_choice"));
    assert!(!dot.contains("transaction_valid"));
    assert!(dot.contains("BAD STATE"));
    let live_symbols = monitor
        .live_registers
        .values()
        .map(|&register| graph.symbol_expr(register).unwrap())
        .collect::<FxHashSet<_>>();
    for (_, node) in graph.nodes() {
        for edge in &node.transitions {
            assert!(
                find_symbols(&ctx, edge.guard)
                    .into_iter()
                    .all(|symbol| live_symbols.contains(&symbol)),
                "ALU edges must read live flags; sampled opcode checks belong in actions"
            );
        }
    }
    for operation in 0..4 {
        let mut execution = Execution::new(&ctx, &monitor);
        assert!(execution.sample(&ctx, &monitor, &symbols, &[("op", operation)]));
        for protocol in 0..4 {
            let live = graph
                .symbol_expr(monitor.live_registers[&(protocol, 0)])
                .unwrap();
            assert_eq!(
                execution.values[&live].to_bool(),
                Some(protocol == operation as usize)
            );
        }
    }
}

#[test]
fn ambiguity_is_assumed_away_without_generating_a_check() {
    let (protocols, mut symbols) = from_source(
        r#"
        struct Dut { out a: u1, }
        prot first<DUT: Dut>(p: u1) { assert_eq(p, DUT.a); step(); }
        prot second<DUT: Dut>(p: u1) { assert_eq(p, DUT.a); step(); }
    "#,
    );
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let mut execution = Execution::new(&ctx, &monitor);
    assert!(execution.sample(&ctx, &monitor, &symbols, &[("a", 1)]));
    assert_eq!(
        monitor.control.graph[monitor.control.graph.entry]
            .transitions
            .iter()
            .filter(|edge| !eval_bv_expr(&ctx, &execution.values, edge.guard).is_zero())
            .count(),
        2,
        "both choices remain enabled when the uniqueness assumption is violated"
    );
    for protocol in 0..2 {
        let live = monitor
            .control
            .graph
            .symbol_expr(monitor.live_registers[&(protocol, 0)])
            .unwrap();
        assert!(execution.values[&live].is_true());
    }
    assert!(!monitor.control.graph.nodes().any(|(_, data)| {
        data.actions
            .iter()
            .any(|a| matches!(monitor.control.graph[a.op], Op::InternalAssertFalse))
    }));
}

#[test]
fn a_dead_ongoing_instance_cannot_revive_and_cannot_complete() {
    let (protocols, mut symbols) = from_source(
        r#"
        struct Dut { out start: u1, out a: u2, out b: u2, }
        prot check<DUT: Dut>(p: u2) {
            assert_eq(DUT.start, 1'b1); assert_eq(p, DUT.a); step();
            assert_eq(p, DUT.b); step();
        }
    "#,
    );
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let mut execution = Execution::new(&ctx, &monitor);
    assert!(execution.sample(&ctx, &monitor, &symbols, &[("start", 1), ("a", 3)]));
    assert!(!execution.sample(&ctx, &monitor, &symbols, &[("b", 2)]));
    let live = monitor
        .control
        .graph
        .symbol_expr(monitor.live_registers[&(0, 0)])
        .unwrap();
    assert!(execution.values[&live].is_false());
    assert_eq!(execution.node, monitor.bad_state);
    assert!(!execution.can_finish(&ctx, &monitor));
    assert!(!execution.sample(&ctx, &monitor, &symbols, &[("b", 3)]));
    assert!(execution.values[&live].is_false());
}

const FAIL_PIPELINE: &str = r#"
struct Dut { out start: u2, out a: u2, out b: u2, }
prot work<DUT: Dut>(p: u2) {
    assert_eq(DUT.start, 2'd1); assert_eq(p, DUT.a); step();
    fork(); assert_eq(p, DUT.b); step();
}
prot idle<DUT: Dut>() { assert_eq(DUT.start, 2'd0); step(); }
"#;

#[test]
fn choice_edges_require_the_older_instance_and_select_only_live_candidates() {
    let (protocols, mut symbols) = from_source(FAIL_PIPELINE);
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let mut execution = Execution::new(&ctx, &monitor);
    assert!(execution.sample(&ctx, &monitor, &symbols, &[("start", 1), ("a", 3)]));
    let node = execution.node;
    assert!(monitor.control.choice_slots.contains_key(&node));
    // This choice runs the older work transaction alongside two fresh attempts.
    let old_work = monitor
        .control
        .graph
        .symbol_expr(monitor.live_registers[&(0, 0)])
        .unwrap();
    let new_work = monitor
        .control
        .graph
        .symbol_expr(monitor.live_registers[&(0, 1)])
        .unwrap();
    let new_idle = monitor
        .control
        .graph
        .symbol_expr(monitor.live_registers[&(1, 0)])
        .unwrap();
    for flags in 0..8 {
        let old = flags & 1 != 0;
        let work = flags & 2 != 0;
        let idle = flags & 4 != 0;
        let values = FxHashMap::from_iter([
            (old_work, BitVecValue::from_u64(u64::from(old), 1)),
            (new_work, BitVecValue::from_u64(u64::from(work), 1)),
            (new_idle, BitVecValue::from_u64(u64::from(idle), 1)),
        ]);
        let enabled = monitor.control.graph[node]
            .transitions
            .iter()
            .enumerate()
            .filter(|(_, edge)| eval_bv_expr(&ctx, &values, edge.guard).is_true())
            .collect::<Vec<_>>();
        if !old || !(work || idle) {
            assert_eq!(enabled.len(), 1);
            assert_eq!(enabled[0].1.target, monitor.bad_state);
        } else {
            let choices = enabled
                .iter()
                .map(|(index, edge)| {
                    assert_ne!(edge.target, monitor.bad_state);
                    monitor.control.transition_kinds[&(node, *index)]
                })
                .collect::<Vec<_>>();
            assert_eq!(choices.contains(&JointTransitionKind::Launch(0)), work);
            assert_eq!(choices.contains(&JointTransitionKind::Launch(1)), idle);
            assert_eq!(choices.len(), usize::from(work) + usize::from(idle));
        }
    }
}

#[test]
fn all_choices_failing_goes_to_bad_state_including_with_a_surviving_post() {
    let (protocols, mut symbols) = from_source(FAIL_PIPELINE);
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    assert!(monitor.control.graph[monitor.bad_state].actions.is_empty());
    let edges = &monitor.control.graph[monitor.bad_state].transitions;
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].target, monitor.bad_state);
    assert_eq!(edges[0].guard, ctx.get_true());
    for with_post in [false, true] {
        let mut execution = Execution::new(&ctx, &monitor);
        if with_post {
            assert!(execution.sample(&ctx, &monitor, &symbols, &[("start", 1), ("a", 3)]));
        }
        assert!(!execution.sample(&ctx, &monitor, &symbols, &[("start", 2), ("b", 3)]));
        assert_eq!(execution.node, monitor.bad_state);
        if with_post {
            let live = monitor
                .control
                .graph
                .symbol_expr(monitor.live_registers[&(0, 0)])
                .unwrap();
            assert!(
                execution.values[&live].is_true(),
                "the older post survived; all new choices failed"
            );
        }
        assert!(!execution.can_finish(&ctx, &monitor));
        assert!(!execution.sample(
            &ctx,
            &monitor,
            &symbols,
            &[("start", 1), ("a", 3), ("b", 3)]
        ));
        assert_eq!(execution.node, monitor.bad_state);
    }
}

#[test]
fn a_failing_post_overrides_a_surviving_new_choice() {
    let (protocols, mut symbols) = from_source(FAIL_PIPELINE);
    let mut ctx = Context::default();
    let monitor = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    let mut execution = Execution::new(&ctx, &monitor);
    assert!(execution.sample(&ctx, &monitor, &symbols, &[("start", 1), ("a", 3)]));
    assert!(!execution.sample(
        &ctx,
        &monitor,
        &symbols,
        &[("start", 1), ("a", 2), ("b", 1)]
    ));
    assert_eq!(execution.node, monitor.bad_state);
    for (slot, expected) in [(0, false), (1, true)] {
        let live = monitor
            .control
            .graph
            .symbol_expr(monitor.live_registers[&(0, slot)])
            .unwrap();
        assert_eq!(execution.values[&live].to_bool(), Some(expected));
    }
}

#[test]
fn constraints_are_lowered_before_composition_and_overlap_failures_reach_bad_state() {
    let (protocols, mut symbols) = selected(
        "src/ir/driver_to_monitor/fixtures/overlapping_slices.prot",
        &["overlapping_slices"],
    );
    let mut ctx = Context::default();
    let naive = prepare_joint_protocols(&mut ctx, &protocols, &symbols)
        .unwrap()
        .into_iter()
        .map(|source| convert_driver_to_monitor(&mut ctx, source, &mut symbols).unwrap())
        .collect::<Vec<_>>();
    let mut lowered = naive[0].clone();
    lower_constraints(&mut ctx, &mut lowered);
    assert!(!lowered.graph.nodes().any(|(_, node)| {
        node.actions
            .iter()
            .any(|action| matches!(lowered.graph[action.op], Op::AssertEq(..)))
    }));
    assert!(lowered.graph.nodes().any(|(_, node)| node.actions.iter().any(|a| {
        matches!(&lowered.graph[a.op], Op::Assign(target, assignment) if *target == lowered.live_register && assignment.concretes.iter().any(|&(guard, value)| guard != ctx.get_true() && value == ctx.get_false()))
    })));
    let naive =
        compose_joint_monitor_automaton(&mut ctx, protocols.clone(), naive, &mut symbols).unwrap();
    let optimized = build_joint_monitor_automaton(&mut ctx, protocols, &mut symbols).unwrap();
    for monitor in [&naive, &optimized] {
        assert!(!monitor.control.graph.nodes().any(|(_, node)| {
            node.actions
                .iter()
                .any(|action| matches!(monitor.control.graph[action.op], Op::AssertEq(..)))
        }));
        for a in 0..8 {
            for b in 0..8 {
                let expected = a >> 1 == b & 3;
                let mut execution = Execution::new(&ctx, monitor);
                assert_eq!(
                    execution.sample(&ctx, monitor, &symbols, &[("a", a), ("b", b)]),
                    expected
                );
                assert_eq!(execution.node == monitor.bad_state, !expected);
            }
        }
    }
}
