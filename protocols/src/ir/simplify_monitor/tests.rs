use super::*;
use crate::frontend;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::require_single_module;
use crate::ir::driver_to_monitor::convert_driver_to_monitor;
use crate::ir::edge_contract::contract_edges;
use crate::ir::lowering::lower_ast_to_ir;
use crate::ir::propagate_assigns::propagate_assignments;
use crate::ir::proto_graph::{Node, Transition};
use crate::ir::reaching_defs::reaching_definitions;
use baa::BitVecValue;
use patronus::expr::eval_bv_expr;

type Values = FxHashMap<ExprRef, BitVecValue>;

fn prepared(source: &str) -> (Context, ProtoGraph, SymbolTable) {
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

fn converted(source: &str) -> (Context, MonitorAutomaton, SymbolTable) {
    let (mut ctx, graph, mut symbols) = prepared(source);
    let monitor = convert_driver_to_monitor(&mut ctx, graph, &mut symbols).unwrap();
    (ctx, monitor, symbols)
}

fn pin(monitor: &MonitorAutomaton, symbols: &SymbolTable, name: &str) -> ExprRef {
    let id = monitor
        .graph
        .dut_pins(symbols)
        .find(|id| symbols[*id].name() == name)
        .unwrap();
    monitor.graph.symbol_expr(id).unwrap()
}

fn init(ctx: &Context, monitor: &MonitorAutomaton, symbols: &SymbolTable) -> Values {
    let mut values = Values::default();
    for (&register, &init) in &monitor.register_inits {
        let value = eval_bv_expr(ctx, &values, init);
        values.insert(monitor.graph.symbol_expr(register).unwrap(), value);
    }
    for id in monitor.graph.dut_pins(symbols) {
        let expr = monitor.graph.symbol_expr(id).unwrap();
        values.insert(expr, BitVecValue::zero(expr.get_bv_type(ctx).unwrap()));
    }
    values
}

fn samples(
    ctx: &Context,
    monitor: &MonitorAutomaton,
    symbols: &SymbolTable,
    values: &mut Values,
    inputs: &[(&str, u64)],
) {
    for &(name, value) in inputs {
        let expr = pin(monitor, symbols, name);
        values.insert(
            expr,
            BitVecValue::from_u64(value, expr.get_bv_type(ctx).unwrap()),
        );
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Step {
    consistent: bool,
    internal_error: bool,
    done: bool,
    forks: usize,
    next: Option<NodeId>,
}

fn step(ctx: &Context, monitor: &MonitorAutomaton, node: NodeId, values: &mut Values) -> Step {
    let graph = &monitor.graph;
    let eval = |expr| eval_bv_expr(ctx, values, expr);
    let mut result = Step {
        consistent: true,
        internal_error: false,
        done: false,
        forks: 0,
        next: None,
    };
    let mut updates = Vec::new();
    for action in &graph[node].actions {
        if eval(action.guard).is_zero() {
            continue;
        }
        match &graph[action.op] {
            Op::AssertEq(a, b) => result.consistent &= eval(*a) == eval(*b),
            Op::InternalAssertFalse => result.internal_error = true,
            Op::Done => result.done = true,
            Op::Fork => result.forks += 1,
            Op::Assign(register, assignment) => {
                assert_eq!(action.guard, ctx.get_true());
                assert!(eval(assignment.dont_care).is_zero());
                if let Some(&(_, rhs)) = assignment
                    .concretes
                    .iter()
                    .find(|(g, _)| !eval(*g).is_zero())
                {
                    updates.push((graph.symbol_expr(*register).unwrap(), eval(rhs)));
                }
            }
        }
    }
    result.next = graph[node]
        .transitions
        .iter()
        .find(|t| !eval(t.guard).is_zero())
        .map(|t| t.target);
    values.extend(updates);
    result
}

fn assert_outputs_equal(
    ctx: &Context,
    a: &MonitorAutomaton,
    b: &MonitorAutomaton,
    node: NodeId,
    av: &Values,
    bv: &Values,
) {
    for arg in &a.graph.args {
        let arg = arg.symbol();
        let ak = eval_bv_expr(ctx, av, a.knownness_outputs[&node][&arg]);
        let bk = eval_bv_expr(ctx, bv, b.knownness_outputs[&node][&arg]);
        assert_eq!(ak, bk, "knownness at {node}, {arg}");
        let va = &av[&a.graph.symbol_expr(a.value_registers[&arg]).unwrap()];
        let vb = &bv[&b.graph.symbol_expr(b.value_registers[&arg]).unwrap()];
        assert_eq!(
            va.and(&ak),
            vb.and(&bk),
            "known value bits at {node}, {arg}"
        );
    }
}

fn compare_trace(
    ctx: &Context,
    a: &MonitorAutomaton,
    b: &MonitorAutomaton,
    symbols: &SymbolTable,
    trace: &[&[(&str, u64)]],
) -> bool {
    let mut av = init(ctx, a, symbols);
    let mut bv = init(ctx, b, symbols);
    let mut node = a.graph.entry;
    for inputs in trace {
        samples(ctx, a, symbols, &mut av, inputs);
        samples(ctx, b, symbols, &mut bv, inputs);
        assert_outputs_equal(ctx, a, b, node, &av, &bv);
        let a_step = step(ctx, a, node, &mut av);
        let b_step = step(ctx, b, node, &mut bv);
        assert_eq!(a_step, b_step, "at {node}, inputs={inputs:?}");
        if !a_step.consistent {
            return false;
        }
        if let Some(next) = a_step.next {
            assert_outputs_equal(ctx, a, b, next, &av, &bv);
            node = next;
        } else {
            break;
        }
    }
    true
}

fn count_checks(monitor: &MonitorAutomaton, node: NodeId) -> usize {
    monitor.graph[node]
        .actions
        .iter()
        .filter(|a| matches!(monitor.graph[a.op], Op::AssertEq(..)))
        .count()
}

#[test]
fn straight_line_binding_removes_masks_and_later_learning() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { in a: u2, out b: u2, }
        prot test<dut: Dut>(p: u2, unused: u3) {
            dut.a := p;
            step();
            dut.a := X;
            assert_eq(p, dut.b);
            fork();
            step();
        }
    "#,
    );
    let analysis = analyze_knownness(&ctx, &original);
    let arg = original.graph.args[0].symbol();
    let mask = original.knownness_registers[&arg];
    let entry = original.graph.entry;
    let next = original.graph[entry].transitions[0].target;
    assert!(
        analysis.node_entry[&entry][&mask]
            .constant()
            .unwrap()
            .is_zero()
    );
    assert!(
        analysis.node_entry[&next][&mask]
            .constant()
            .unwrap()
            .is_all_ones()
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    assert!(optimized.knownness_registers.is_empty());
    assert_eq!(optimized.register_inits.len(), 3); // two value registers and live
    assert_eq!(count_checks(&optimized, entry), 0);
    assert_eq!(optimized.graph[entry].actions.len(), 1);
    assert_eq!(count_checks(&optimized, next), 1);
    assert!(
        !optimized.graph[next]
            .actions
            .iter()
            .any(|a| matches!(optimized.graph[a.op], Op::Assign(..)))
    );
    for a in 0..4 {
        for b in 0..4 {
            assert_eq!(
                compare_trace(
                    &ctx,
                    &original,
                    &optimized,
                    &symbols,
                    &[&[("a", a)], &[("b", b)], &[]]
                ),
                a == b
            );
        }
    }
}

#[test]
fn same_cycle_overlap_preserves_conflicts_and_inferred_bits() {
    let (mut ctx, original, mut symbols) = converted(include_str!(
        "../driver_to_monitor/fixtures/overlapping_slices.prot"
    ));
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    let entry = optimized.graph.entry;
    assert!(optimized.knownness_registers.is_empty());
    assert_eq!(count_checks(&original, entry), 2);
    assert_eq!(count_checks(&optimized, entry), 1);
    for a in 0..8 {
        for b in 0..8 {
            // Independent direct equality oracle for the shared bits p[3:2].
            assert_eq!(
                compare_trace(
                    &ctx,
                    &original,
                    &optimized,
                    &symbols,
                    &[&[("a", a), ("b", b)]]
                ),
                a >> 1 == b & 3
            );
        }
    }
    let dot = optimized.to_dot_string(&ctx, &symbols);
    if let Some(path) = std::env::var_os("PROTOCOLS_SIMPLIFIED_MONITOR_DOT") {
        std::fs::write(path, &dot).unwrap();
    }
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path("../../tests/snapshots");
    settings.bind(|| insta::assert_snapshot!("overlapping_slices_simplified", dot));
}

#[test]
fn branch_join_retains_dynamic_knownness_and_compresses_a_whole_mask() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { in a: u3, out b: u3, out g: u1, }
        prot test<dut: Dut>(p: u3) {
            if dut.g { dut.a := p; }
            step();
            dut.a := X;
            assert_eq(p, dut.b);
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    let arg = original.graph.args[0].symbol();
    let mask = optimized.knownness_registers[&arg];
    assert_eq!(symbols[mask].tpe(), Type::BitVec(1));
    assert_ne!(mask, original.knownness_registers[&arg]);
    for g in 0..2 {
        for a in 0..8 {
            for b in 0..8 {
                assert_eq!(
                    compare_trace(
                        &ctx,
                        &original,
                        &optimized,
                        &symbols,
                        &[&[("g", g), ("a", a)], &[("b", b)], &[]]
                    ),
                    g == 0 || a == b
                );
            }
        }
    }
}

#[test]
fn loop_keeps_first_iteration_distinct_from_later_iterations() {
    let (mut ctx, mut original, mut symbols) = converted(
        r#"
        struct Dut { out a: u2, out stop: u1, }
        prot test<dut: Dut>(p: u2) {
            if !(dut.stop) { assert_eq(p, dut.a); }
            step();
        }
    "#,
    );
    let entry = original.graph.entry;
    // Make the same control node serve the first and subsequent observations,
    // so analysis must merge initialization with the backedge at entry itself.
    let done = original.graph[entry].transitions[0].target;
    let stop = pin(&original, &symbols, "stop");
    let not_stop = original.graph.not_guard(&mut ctx, stop);
    original.graph.node_mut(entry).transitions = vec![
        Transition::new(not_stop, entry, true),
        Transition::new(stop, done, true),
    ];
    let arg = original.graph.args[0].symbol();
    let analysis = analyze_knownness(&ctx, &original);
    let fact = &analysis.node_entry[&entry][&original.knownness_registers[&arg]];
    assert_eq!(fact, &KnownBits::unknown(2));
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    assert_eq!(
        symbols[optimized.knownness_registers[&arg]].tpe(),
        Type::BitVec(1)
    );
    for a in 0..4 {
        for b in 0..4 {
            assert_eq!(
                compare_trace(
                    &ctx,
                    &original,
                    &optimized,
                    &symbols,
                    &[
                        &[("a", a), ("stop", 0)],
                        &[("a", b), ("stop", 0)],
                        &[("stop", 1)],
                        &[]
                    ]
                ),
                a == b
            );
        }
    }
    // Exiting without observing anything leaves the logical mask zero.
    assert!(compare_trace(
        &ctx,
        &original,
        &optimized,
        &symbols,
        &[&[("stop", 1)], &[]]
    ));
}

#[test]
fn independently_learned_slices_keep_the_bit_vector_mask() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u1, out b: u1, out g: u1, out h: u1, out all: u2, }
        prot test<dut: Dut>(p: u2) {
            if dut.g { assert_eq(p[0], dut.a); }
            if dut.h { assert_eq(p[1], dut.b); }
            step();
            assert_eq(p, dut.all);
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    let arg = original.graph.args[0].symbol();
    assert_eq!(
        symbols[optimized.knownness_registers[&arg]].tpe(),
        Type::BitVec(2)
    );
    for g in 0..2 {
        for h in 0..2 {
            for a in 0..2 {
                for b in 0..2 {
                    for all in 0..4 {
                        let expected = (g == 0 || all & 1 == a) && (h == 0 || all >> 1 == b);
                        assert_eq!(
                            compare_trace(
                                &ctx,
                                &original,
                                &optimized,
                                &symbols,
                                &[
                                    &[("g", g), ("h", h), ("a", a), ("b", b)],
                                    &[("all", all)],
                                    &[]
                                ]
                            ),
                            expected
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn exhaustive_guarded_overlaps_and_concatenations_match_direct_constraints() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u4, out b: u2, out g: u1, out h: u1, out all: u3, }
        prot test<dut: Dut>(p: u3, q: u2) {
            if dut.g { assert_eq(p[2:1] ## q, dut.a); }
            if dut.h { assert_eq(p[1:0], dut.b); }
            step();
            assert_eq(p, dut.all);
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    for g in 0..2 {
        for h in 0..2 {
            for a in 0..16 {
                for b in 0..4 {
                    for all in 0..8 {
                        // Direct oracle: both partial observations must agree
                        // with the later whole value. q can take a[1:0].
                        let expected = (g == 0 || all >> 1 == a >> 2) && (h == 0 || all & 3 == b);
                        assert_eq!(
                            compare_trace(
                                &ctx,
                                &original,
                                &optimized,
                                &symbols,
                                &[
                                    &[("g", g), ("h", h), ("a", a), ("b", b)],
                                    &[("all", all)],
                                    &[],
                                ]
                            ),
                            expected,
                            "g={g}, h={h}, a={a}, b={b}, all={all}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn correlated_partial_bindings_conservatively_keep_the_mask() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u1, out b: u1, out g: u1, out all: u2, }
        prot test<dut: Dut>(p: u2) {
            if dut.g {
                assert_eq(p[1], dut.a);
                assert_eq(p[0], dut.b);
            }
            step();
            assert_eq(p, dut.all);
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    let argument = original.graph.args[0].symbol();
    assert_eq!(
        symbols[optimized.knownness_registers[&argument]].tpe(),
        Type::BitVec(2)
    );
    for g in 0..2 {
        for a in 0..2 {
            for b in 0..2 {
                for all in 0..4 {
                    assert_eq!(
                        compare_trace(
                            &ctx,
                            &original,
                            &optimized,
                            &symbols,
                            &[&[("g", g), ("a", a), ("b", b)], &[("all", all)], &[],]
                        ),
                        g == 0 || all == (a << 1) | b
                    );
                }
            }
        }
    }
}

#[test]
fn a_lowered_loop_preserves_knownness_after_zero_or_multiple_iterations() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u2, out stop: u1, }
        prot test<dut: Dut>(p: u2) {
            while !(dut.stop) { assert_eq(p, dut.a); step(); }
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    // The initial control node and later loop iterations are distinct, but the
    // shared completion node still needs to report whether any binding occurred.
    let argument = original.graph.args[0].symbol();
    assert_eq!(
        symbols[optimized.knownness_registers[&argument]].tpe(),
        Type::BitVec(1)
    );
    for a in 0..4 {
        for b in 0..4 {
            assert_eq!(
                compare_trace(
                    &ctx,
                    &original,
                    &optimized,
                    &symbols,
                    &[
                        &[("a", a), ("stop", 0)],
                        &[("a", b), ("stop", 0)],
                        &[("stop", 1)],
                        &[],
                    ]
                ),
                a == b
            );
        }
    }
}

#[test]
fn edge_guards_refine_the_source_updates_before_the_successor() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u2, out b: u2, out g: u1, }
        prot test<dut: Dut>(p: u2) {
            if dut.g {
                assert_eq(p, dut.a);
                step();
                assert_eq(p, dut.b);
                step();
            } else {
                step();
                step();
            }
            step();
        }
    "#,
    );
    let analysis = analyze_knownness(&ctx, &original);
    let b = pin(&original, &symbols, "b");
    let arg = original.graph.args[0].symbol();
    let mask = original.knownness_registers[&arg];
    let check_b = original
        .graph
        .nodes()
        .find(|(_, node)| {
            node.actions.iter().any(|a| {
                op_reads(&original.graph[a.op])
                    .iter()
                    .any(|&e| find_symbols(&ctx, e).contains(&b))
            })
        })
        .unwrap()
        .0;
    assert!(
        analysis.node_entry[&check_b][&mask]
            .constant()
            .unwrap()
            .is_all_ones()
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    for g in 0..2 {
        for b in 0..4 {
            assert_eq!(
                compare_trace(
                    &ctx,
                    &original,
                    &optimized,
                    &symbols,
                    &[&[("g", g), ("a", 2)], &[("b", b)], &[], &[]]
                ),
                g == 0 || b == 2
            );
        }
    }
}

#[test]
#[should_panic(expected = "prune unreachable nodes before knownness analysis")]
fn unreachable_nodes_violate_the_analysis_precondition() {
    let (ctx, mut original, _) = converted(
        r#"
        struct Dut { out a: u2, }
        prot test<dut: Dut>(p: u2) { assert_eq(p, dut.a); step(); }
    "#,
    );
    original.graph.n(Node::empty());
    analyze_knownness(&ctx, &original);
}

#[test]
fn wide_masks_and_extensions_are_simplified_without_host_integer_limits() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u5, out b: u130, }
        prot test<dut: Dut>(p: u130) {
            assert_eq(p[129:125], dut.a);
            step();
            assert_eq(p, dut.b);
            step();
        }
    "#,
    );
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    assert!(optimized.knownness_registers.is_empty());
    let mut av = init(&ctx, &original, &symbols);
    let mut bv = init(&ctx, &optimized, &symbols);
    samples(&ctx, &original, &symbols, &mut av, &[("a", 31)]);
    samples(&ctx, &optimized, &symbols, &mut bv, &[("a", 31)]);
    let entry = original.graph.entry;
    assert_eq!(
        step(&ctx, &original, entry, &mut av),
        step(&ctx, &optimized, entry, &mut bv)
    );
    let next = original.graph[entry].transitions[0].target;
    assert_outputs_equal(&ctx, &original, &optimized, next, &av, &bv);
    let arg = original.graph.args[0].symbol();
    let known = eval_bv_expr(&ctx, &bv, optimized.knownness_outputs[&next][&arg]);
    assert_eq!(known.slice(129, 125), BitVecValue::ones(5));
    assert!(known.slice(124, 0).is_zero());
    for input in [BitVecValue::ones(130), BitVecValue::zero(130)] {
        let (mut av, mut bv) = (av.clone(), bv.clone());
        av.insert(pin(&original, &symbols, "b"), input.clone());
        bv.insert(pin(&optimized, &symbols, "b"), input.clone());
        let result = step(&ctx, &original, next, &mut av);
        assert_eq!(result, step(&ctx, &optimized, next, &mut bv));
        assert_eq!(result.consistent, input.is_all_ones());
    }
}

#[test]
fn nested_ites_constants_and_multiple_parameters_remain_equivalent() {
    let (mut ctx, mut driver, mut symbols) = prepared(
        r#"
        struct Dut { in a: u2, out b: u2, out g: u1, out h: u1, }
        prot test<dut: Dut>(p: u2, q: u2) {
            dut.a := p;
            step();
            dut.a := X;
            assert_eq(q, dut.b);
            step();
        }
    "#,
    );
    let p = driver.symbol_expr(driver.args[0].symbol()).unwrap();
    let q = driver.symbol_expr(driver.args[1].symbol()).unwrap();
    let g = driver
        .dut_pins(&symbols)
        .find(|id| symbols[*id].name() == "g")
        .unwrap();
    let h = driver
        .dut_pins(&symbols)
        .find(|id| symbols[*id].name() == "h")
        .unwrap();
    let g = driver.symbol_expr(g).unwrap_or_else(|| {
        let expr = ctx.bv_symbol("dut.g", 1);
        driver.cache_symbol_expr(g, expr);
        expr
    });
    let h = driver.symbol_expr(h).unwrap_or_else(|| {
        let expr = ctx.bv_symbol("dut.h", 1);
        driver.cache_symbol_expr(h, expr);
        expr
    });
    let constant = ctx.bit_vec_val(2, 2);
    let inner = ctx.ite(h, p, constant);
    let pattern = ctx.ite(g, inner, q);
    for (_, op) in driver.ops_mut() {
        if let Op::Assign(_, assignment) = op {
            for (_, rhs) in &mut assignment.concretes {
                if *rhs == p {
                    *rhs = pattern;
                }
            }
        }
    }
    let original = convert_driver_to_monitor(&mut ctx, driver, &mut symbols).unwrap();
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    for g in 0..2 {
        for h in 0..2 {
            for a in 0..4 {
                for b in 0..4 {
                    let expected = if g == 0 { a == b } else { h == 1 || a == 2 };
                    assert_eq!(
                        compare_trace(
                            &ctx,
                            &original,
                            &optimized,
                            &symbols,
                            &[&[("g", g), ("h", h), ("a", a)], &[("b", b)], &[]]
                        ),
                        expected
                    );
                }
            }
        }
    }
}

#[test]
fn dead_actions_tautologies_and_internal_errors_stay_separate() {
    let (mut ctx, mut original, mut symbols) = converted(
        r#"
        struct Dut { out a: u2, }
        prot test<dut: Dut>() { assert_eq(dut.a, 2'b01); step(); }
    "#,
    );
    let entry = original.graph.entry;
    let true_id = ctx.get_true();
    let false_id = ctx.get_false();
    let op = original.graph.o(Op::InternalAssertFalse);
    original.graph.push_action(entry, Action::new(false_id, op));
    let tautology = original.graph.o(Op::AssertEq(true_id, true_id));
    original
        .graph
        .push_action(entry, Action::new(true_id, tautology));
    let optimized = simplify_monitor(&mut ctx, original.clone(), &mut symbols);
    assert_eq!(optimized.graph[entry].actions.len(), 1);
    for a in 0..4 {
        assert_eq!(
            compare_trace(&ctx, &original, &optimized, &symbols, &[&[("a", a)], &[]]),
            a == 1
        );
    }
}

#[test]
fn simplifying_twice_preserves_the_result_and_logical_output_widths() {
    let (mut ctx, original, mut symbols) = converted(
        r#"
        struct Dut { out a: u4, out g: u1, }
        prot test<dut: Dut>(p: u4) {
            while dut.g { assert_eq(p, dut.a); step(); }
            step();
        }
    "#,
    );
    let once = simplify_monitor(&mut ctx, original, &mut symbols);
    let twice = simplify_monitor(&mut ctx, once.clone(), &mut symbols);
    assert_eq!(once.register_inits, twice.register_inits);
    assert_eq!(once.knownness_registers, twice.knownness_registers);
    for outputs in twice.knownness_outputs.values() {
        for expr in outputs.values() {
            assert_eq!(expr.get_bv_type(&ctx), Some(4));
        }
    }
    assert!(compare_trace(
        &ctx,
        &once,
        &twice,
        &symbols,
        &[
            &[("g", 1), ("a", 5)],
            &[("g", 1), ("a", 5)],
            &[("g", 0)],
            &[]
        ]
    ));
}
