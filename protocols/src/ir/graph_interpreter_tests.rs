use super::*;
use crate::frontend;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::symbol::Dir;
use crate::frontend::{Module, require_single_module};
use crate::ir::edge_contract::{contract_edges, normalize_assignments};
use crate::ir::lowering::lower_ast_to_ir;
use crate::ir::propagate_assigns::{insert_assignment_registers, simplify_assignments};
use patronus::system::{State, TransitionSystem};

fn load(filename: &str) -> (SymbolTable, Module) {
    let mut handler = DiagnosticHandler::default();
    let (symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
    (
        symbols,
        require_single_module(modules, &[filename]).unwrap(),
    )
}

fn mock_dut(ctx: &mut Context, module: &Module) -> PatronusSim {
    let mut system = TransitionSystem::new("loop_test".into());
    let mut inputs = FxHashMap::default();
    for pin in &module.pins {
        if pin.dir() == Dir::In {
            let expr = ctx.bv_symbol(pin.name(), pin.bitwidth());
            system.add_input(ctx, expr);
            inputs.insert(pin.name(), expr);
        }
    }
    let phase = ctx.bv_symbol("phase", 1);
    let next = ctx.not(phase);
    system.add_state(
        ctx,
        State {
            symbol: phase,
            init: Some(ctx.get_false()),
            next: Some(next),
        },
    );
    let echo = inputs.get("data").map(|&data| {
        let echo = ctx.bv_symbol("saved_data", 8);
        let init = ctx.bit_vec_val(0, 8);
        system.add_state(
            ctx,
            State {
                symbol: echo,
                init: Some(init),
                next: Some(data),
            },
        );
        echo
    });
    for pin in &module.pins {
        if pin.dir() == Dir::Out {
            let expr = match pin.name() {
                "ready" | "ACK" => phase,
                "echo" => echo.unwrap(),
                _ => ctx.bit_vec_val(0, pin.bitwidth()),
            };
            system.add_output(ctx, pin.name().to_owned().into(), expr);
        }
    }
    PatronusSim::from_system(ctx, system, module, None).unwrap()
}

fn prepared(
    ctx: &mut Context,
    symbols: &mut SymbolTable,
    ast: crate::frontend::ast::Protocol,
) -> ProtoGraph {
    let mut graph = lower_ast_to_ir(ctx, ast, symbols);
    contract_edges(ctx, &mut graph, symbols);
    let entry = graph.entry;
    let initial = insert_assignment_registers(ctx, &mut graph, symbols, entry);
    simplify_assignments(ctx, &mut graph, symbols, &initial);
    normalize_assignments(ctx, &mut graph, symbols);
    graph.garbage_collect_unreachable(ctx);
    graph
}

fn scalar(value: u64, width: u32) -> ArgValue {
    BitVecValue::from_u64(value, width).into()
}

fn sequence(values: &[u64], width: u32) -> ArgValue {
    values
        .iter()
        .map(|v| BitVecValue::from_u64(*v, width))
        .collect::<Vec<_>>()
        .into()
}

fn compare_trace(
    filename: &str,
    trace: &[(String, Vec<ArgValue>)],
    create_dut: impl Fn(&mut Context, &Module) -> PatronusSim,
) -> Vec<GraphInterpretResult> {
    let (mut symbols, module) = load(filename);
    let mut ctx = Context::default();
    let mut dut = create_dut(&mut ctx, &module);
    let mut reference_ctx = Context::default();
    let mut reference_dut = create_dut(&mut reference_ctx, &module);
    let mut results = Vec::new();
    for (name, arguments) in trace {
        let ast = module
            .protos
            .iter()
            .find(|p| p.name == *name)
            .unwrap()
            .clone();
        let graph = prepared(&mut ctx, &mut symbols, ast);
        let args = graph
            .args
            .iter()
            .zip(arguments)
            .map(|(a, v)| (symbols[a.symbol()].name(), v.clone()))
            .collect();
        let result = interpret(&ctx, &graph, &symbols, args, &mut dut);
        assert!(result.failure.is_none(), "{name}: {:?}", result.failure);
        // Step the existing AST evaluator directly: only source step() statements
        // produce samples, including when the final statement is a loop.
        let ast = module.protos.iter().find(|p| p.name == *name).unwrap();
        let args = ast
            .args
            .iter()
            .zip(arguments.iter().cloned())
            .map(|(a, v)| (symbols[a.symbol()].name(), v))
            .collect::<FxHashMap<_, _>>();
        let tx = crate::scheduler::Transaction::new(
            ast,
            &symbols,
            args.clone(),
            ast.next_stmt_mapping(),
        );
        let mut thread = crate::scheduler::Thread::initialize_thread(tx, 0);
        let mut evaluator = crate::interpreter::Evaluator::new(args, ast, &symbols, &reference_dut);
        evaluator.enable_assertions();
        evaluator.init_thread_inputs(&mut reference_dut, 0).unwrap();
        let mut stmt = Some(ast.body);
        let mut steps = 0;
        while let Some(current) = stmt {
            stmt = evaluator
                .evaluate_stmt(&mut reference_dut, current)
                .unwrap();
            if matches!(ast[current], crate::frontend::ast::Stmt::Step) {
                steps += 1;
                assert!(steps < 2000, "AST loop failed to terminate");
                evaluator.finalize_inputs_for_cycle(&mut reference_dut);
                reference_dut.step();
                thread.loop_vars = evaluator.loop_vars.clone();
                thread.loop_info = evaluator.loop_info.clone();
                evaluator.context_switch(thread.clone());
                evaluator.init_thread_inputs(&mut reference_dut, 0).unwrap();
            }
        }
        let expected = evaluator.waveform;
        // Compare driven pins. Outputs following an X drive can differ between
        // simulators; protocol assertions independently check constrained outputs.
        for port in dut.inputs() {
            let actual = result.waveform.get(&port).cloned().unwrap_or_default();
            let expected = expected.get(&port).cloned().unwrap_or_default();
            assert_eq!(
                actual.len(),
                expected.len(),
                "{name}: {} cycle count",
                dut.port_name(port)
            );
            for (cycle, (a, b)) in actual.iter().zip(&expected).enumerate() {
                match (a, b) {
                    (WaveValue::Concrete(a), WaveValue::Concrete(b)) => {
                        assert_eq!(a, b, "{name}: {} cycle {cycle}", dut.port_name(port))
                    }
                    (WaveValue::DontCare, WaveValue::DontCare) => {}
                    _ => panic!(
                        "{name}: {} cycle {cycle}: {a:?} != {b:?}",
                        dut.port_name(port)
                    ),
                }
            }
        }

        results.push(result);
    }
    results
}

fn compare_with_ast(filename: &str, name: &str, arguments: Vec<ArgValue>) {
    compare_trace(filename, &[(name.to_string(), arguments)], mock_dut);
}

#[test]
fn contracted_loop_runtime() {
    let cases = [
        ("for_zero_or_more", vec![sequence(&[], 8)]),
        ("for_zero_or_more", vec![sequence(&[10], 8)]),
        ("for_zero_or_more", vec![sequence(&[10, 20, 30], 8)]),
        ("for_one_or_more", vec![sequence(&[10], 8)]),
        ("for_one_or_more", vec![sequence(&[10, 20, 30], 8)]),
        ("for_distinct", vec![sequence(&[10, 20, 30], 8)]),
        ("repeat_count", vec![scalar(0, 64)]),
        ("repeat_count", vec![scalar(1, 64)]),
        ("repeat_count", vec![scalar(3, 64)]),
        ("repeat_count", vec![scalar(260, 64)]),
        ("two_step_loop", vec![sequence(&[10, 20, 30], 8)]),
        ("step_in_middle", vec![sequence(&[10], 8)]),
        ("step_in_middle", vec![sequence(&[10, 20, 30], 8)]),
        ("conditional_steps", vec![sequence(&[10, 20, 30], 8)]),
        ("conditional_steps", vec![sequence(&[], 8)]),
        ("conditional_steps", vec![sequence(&[10], 8)]),
        ("repeat_literal", vec![]),
        ("frozen_check", vec![sequence(&[10, 20, 30], 8)]),
        ("release_in_loop", vec![sequence(&[10, 20, 30], 8)]),
        ("wait_in_body", vec![sequence(&[10, 20, 30], 8)]),
        (
            "independent_loops",
            vec![sequence(&[10, 20], 8), sequence(&[30, 40], 8)],
        ),
        (
            "independent_loops",
            vec![sequence(&[], 8), sequence(&[10], 8)],
        ),
        (
            "independent_loops",
            vec![sequence(&[10], 8), sequence(&[], 8)],
        ),
    ];
    for (name, args) in cases {
        compare_with_ast("../tests/loops/loops.prot", name, args);
    }
    for name in ["specialized_waits", "hold_after_plain_loop"] {
        for values in [&[][..], &[10][..], &[10, 20, 30][..], &[10; 260][..]] {
            compare_with_ast("../tests/loops/loops.prot", name, vec![sequence(values, 8)]);
        }
    }
    for count in [0, 1, 3, 260] {
        for name in ["specialized_repeat_waits", "plain_repeat_count"] {
            compare_with_ast("../tests/loops/loops.prot", name, vec![scalar(count, 64)]);
        }
    }
}

#[test]
fn explicit_loop_selections() {
    let (symbols, module) = load("../tests/loops/loops.prot");
    for (name, specialized, has_data) in [
        ("for_one_or_more", true, true),
        ("repeat_count", true, false),
        ("for_zero_or_more", false, true),
        ("repeat_literal", false, false),
    ] {
        let mut symbols = symbols.clone();
        let mut ctx = Context::default();
        let ast = module
            .protos
            .iter()
            .find(|p| p.name == name)
            .unwrap()
            .clone();
        let graph = lower_ast_to_ir(&mut ctx, ast, &mut symbols);
        assert_eq!(graph.loops.len(), 1, "{name}");
        let (loop_id, fifo) = graph.loops.iter().next().unwrap();
        let valid = fifo.valid;
        let empty = ctx.not(valid);
        let not_last = ctx.not(fifo.last);
        let non_final = ctx.and(valid, not_last);
        let final_item = ctx.and(valid, fifo.last);
        let nodes = graph.reachable_node_ids(&ctx, graph.entry);
        let heads: Vec<_> = nodes
            .iter()
            .copied()
            .filter(|&n| graph[n].transitions.iter().any(|t| t.guard == empty))
            .collect();
        assert_eq!(heads.len(), 1, "{name}: initial selection");
        let head = &graph[heads[0]];
        assert!(
            head.actions.is_empty(),
            "{name}: empty selection must not load"
        );
        assert_eq!(head.transitions.len(), if specialized { 3 } else { 2 });
        assert!(head.transitions.iter().all(|t| !t.consumes_step));
        if specialized {
            let choices: Vec<_> = head
                .transitions
                .iter()
                .filter(|t| t.guard != empty)
                .cloned()
                .collect();
            assert!(choices.iter().any(|t| t.guard == non_final));
            assert!(choices.iter().any(|t| t.guard == final_item));
            let continuations: Vec<_> = nodes
                .iter()
                .copied()
                .filter(|&n| graph[n].transitions == choices)
                .collect();
            assert_eq!(continuations.len(), 1, "{name}: continuation selection");
            let continuation = &graph[continuations[0]];
            assert_eq!(continuation.actions.len(), 1);
            assert_eq!(continuation.actions[0].guard, empty);
            assert!(matches!(
                graph[continuation.actions[0].op],
                Op::InternalAssertFalse
            ));
        } else {
            assert!(head.transitions.iter().any(|t| t.guard == valid));
        }
        let mut data_loads = Vec::new();
        let mut consumes = Vec::new();
        for node in nodes {
            for action in &graph[node].actions {
                match graph[action.op] {
                    Op::Last { .. } => panic!("{name}: stored last load remains"),
                    Op::Data {
                        loop_id: id,
                        target,
                    } => {
                        assert_eq!(id, loop_id);
                        data_loads.push(target);
                    }
                    Op::Valid {
                        loop_id: id,
                        target,
                    } => {
                        assert_eq!(id, loop_id);
                        consumes.push(target);
                    }
                    _ => {}
                }
            }
        }
        let copies = if specialized { 2 } else { 1 };
        assert_eq!(consumes.len(), copies, "{name}: body copies");
        assert!(consumes.iter().all(|r| *r == consumes[0]));
        assert_eq!(data_loads.len(), if has_data { copies } else { 0 });
        assert!(data_loads.iter().all(|r| *r == data_loads[0]));
        assert!(
            graph
                .register_inits
                .keys()
                .all(|r| !symbols[*r].name().ends_with("_last"))
        );
    }
}

#[test]
fn specialized_conditions_remove_dead_branches() {
    let (mut symbols, module) = load("../tests/loops/loops.prot");
    let mut ctx = Context::default();
    let ast = module
        .protos
        .iter()
        .find(|p| p.name == "conditional_steps")
        .unwrap()
        .clone();
    let graph = lower_ast_to_ir(&mut ctx, ast, &mut symbols);
    let nodes = graph.reachable_node_ids(&ctx, graph.entry);
    // One step per specialized body, plus the step after the loop. Neither
    // copy should include the other branch's step, even before contraction.
    assert_eq!(
        nodes
            .iter()
            .flat_map(|&n| &graph[n].transitions)
            .filter(|t| t.consumes_step)
            .count(),
        3
    );
    assert_eq!(
        nodes
            .iter()
            .filter(|&&n| graph[n].transitions.len() > 1)
            .count(),
        2
    );
}

#[test]
fn loop_paths_without_steps_are_rejected() {
    use crate::frontend::ast::{Expr, Protocol, Stmt};
    let (symbols, module) = load("../tests/loops/loops.prot");
    // Rebuild valid fixtures after frontend checking so the lowerer's own
    // per-copy validation is exercised, including each specialized variant.
    for (name, remove_step) in [
        ("for_zero_or_more", 0),
        ("conditional_steps", 0),
        ("conditional_steps", 1),
    ] {
        let original = module.protos.iter().find(|p| p.name == name).unwrap();
        let (variable, source) = original
            .stmt_ids()
            .into_iter()
            .find_map(|s| {
                if let Stmt::ForInLoop(variable, source, _) = original[s] {
                    Some((variable, source))
                } else {
                    None
                }
            })
            .unwrap();
        let mut ast = Protocol::from_context(original.ctx.clone());
        let empty = ast.s(Stmt::Block(vec![]));
        let body = if name == "conditional_steps" {
            let step = ast.s(Stmt::Step);
            let cond = ast.e(Expr::IsLastIteration);
            let (tru, fals) = if remove_step == 0 {
                (empty, step)
            } else {
                (step, empty)
            };
            ast.s(Stmt::IfElse(cond, tru, fals))
        } else {
            empty
        };
        ast.body = ast.s(Stmt::ForInLoop(variable, source, body));
        let mut symbols = symbols.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = lower_ast_to_ir(&mut Context::default(), ast, &mut symbols);
        }));
        let panic = result.expect_err("loop path without step was accepted");
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(
            message.contains("every iteration path must contain a step()"),
            "{message}"
        );
    }
}

#[test]
fn wishbone_loops_after_all_passes() {
    let filename = "../examples/wishbone/wishbone.prot";
    let (_, module) = load(filename);
    for ast in module.protos {
        let read = ast.name.starts_with("read");
        let arguments = if ast.args.is_empty() {
            vec![]
        } else if ast.name.contains("burst_") && !ast.name.ends_with("single") {
            vec![
                scalar(15, 4),
                scalar(0x34, 32),
                sequence(
                    if read {
                        &[0; 10]
                    } else {
                        &[10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
                    },
                    32,
                ),
            ]
        } else {
            vec![
                scalar(15, 4),
                scalar(0x34, 32),
                scalar(if read { 0 } else { 10 }, 32),
            ]
        };
        compare_with_ast(filename, &ast.name, arguments);
    }
}

#[test]
fn loop_holds_use_saved_pin_values() {
    let filename = "../tests/loops/loops.prot";
    for name in [
        "hold_across_iterations",
        "hold_first_iteration",
        "hold_sampled_choice",
    ] {
        compare_with_ast(filename, name, vec![sequence(&[10, 20, 30], 8)]);
    }
}

#[test]
fn wide_iteration_counter() {
    // The AST interpreter currently caps iter_count at 64 bits; check this
    // wider case against explicit samples instead.
    let (mut symbols, module) = load("../tests/loops/loops.prot");
    let ast = module
        .protos
        .iter()
        .find(|p| p.name == "mixed_index_widths")
        .unwrap()
        .clone();
    let mut ctx = Context::default();
    let mut dut = mock_dut(&mut ctx, &module);
    let graph = prepared(&mut ctx, &mut symbols, ast);
    let args = FxHashMap::from_iter([("values", sequence(&[10, 20, 30], 8))]);
    let result = interpret(&ctx, &graph, &symbols, args, &mut dut);
    assert!(result.failure.is_none());
    for (name, expected) in [("data", vec![10, 21, 32, 32]), ("flag", vec![1, 0, 0, 0])] {
        let port = dut.inputs().find(|p| dut.port_name(*p) == name).unwrap();
        let actual = result.waveform[&port]
            .iter()
            .map(|v| match v {
                WaveValue::Concrete(value) => value.to_u64().unwrap(),
                _ => panic!("unexpected X on {name}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }
}

#[test]
fn wishbone_rtl_bursts() {
    let filename = "../examples/wishbone/wishbone.prot";
    let (symbols, module) = load(filename);
    for transactions in [
        "read_write.tx",
        "4.8_constant_address_burst.tx",
        "4.?_incremental_address_burst.tx",
        "4.?_incremental_address_burst_wrap.tx",
    ] {
        let path = format!("../examples/wishbone/{transactions}");
        let mut handler = DiagnosticHandler::default();
        let traces =
            crate::transaction_frontend(&path, &symbols, &module.protos, &mut handler).unwrap();
        for trace in traces {
            compare_trace(filename, &trace, |ctx, module| {
                PatronusSim::new_with_context(
                    ctx,
                    &[
                        "../examples/wishbone/rtl/dut.v",
                        "../examples/wishbone/rtl/tb.v",
                    ],
                    Some("tb"),
                    module,
                    None,
                )
                .unwrap()
            });
        }
    }
}

type Samples = Vec<FxHashMap<String, BitVecValue>>;

fn driver_samples(
    filename: &str,
    trace: &[(String, Vec<ArgValue>)],
    create_dut: impl Fn(&mut Context, &Module) -> PatronusSim,
) -> Samples {
    let (mut symbols, module) = load(filename);
    let mut ctx = Context::default();
    let mut dut = create_dut(&mut ctx, &module);
    let mut samples = Vec::new();
    for (name, arguments) in trace {
        let ast = module
            .protos
            .iter()
            .find(|p| p.name == *name)
            .unwrap()
            .clone();
        let graph = prepared(&mut ctx, &mut symbols, ast);
        let args = graph
            .args
            .iter()
            .zip(arguments)
            .map(|(a, v)| (symbols[a.symbol()].name(), v.clone()))
            .collect();
        let result = interpret(&ctx, &graph, &symbols, args, &mut dut);
        assert!(result.failure.is_none(), "{name}: {:?}", result.failure);
        for cycle in 0..result.waveform.values().next().unwrap().len() {
            let sample = result
                .waveform
                .iter()
                .map(|(&port, values)| {
                    let value = match &values[cycle] {
                        WaveValue::Concrete(v) => v.clone(),
                        WaveValue::DontCare => BitVecValue::zero(dut.port_width(port)),
                    };
                    (dut.port_name(port).to_string(), value)
                })
                .collect();
            samples.push(sample);
        }
    }
    samples
}

fn monitor_failure(filename: &str, protocols: &[&str], samples: &Samples) -> Option<usize> {
    use crate::backends::monitor_transition_system::into_monitor_transition_system;
    use crate::ir::joint_monitor::build_joint_monitor_automaton;
    use patronus::sim::{InitKind, Interpreter, Simulator};
    let (mut symbols, module) = load(filename);
    let mut ctx = Context::default();
    let selected = module
        .protos
        .iter()
        .filter(|p| protocols.is_empty() || protocols.contains(&p.name.as_str()))
        .cloned()
        .collect();
    let monitor = build_joint_monitor_automaton(&mut ctx, selected, &mut symbols).unwrap();
    let core = into_monitor_transition_system(&mut ctx, &monitor, &module, &symbols);
    let mut sim = Interpreter::new(&ctx, &core.ts);
    sim.init(InitKind::Zero);
    for (cycle, sample) in samples.iter().enumerate() {
        for (&pin, &input) in &core.pin_inputs {
            sim.set(input, &sample[symbols[pin].name()]);
        }
        sim.step();
        assert_eq!(
            sim.get(core.internal_error),
            BitVecValue::from_u64(0, 1).into(),
            "internal monitor error on cycle {cycle}"
        );
        if sim.get(core.bad) == BitVecValue::from_u64(1, 1).into() {
            return Some(cycle);
        }
    }
    None
}

#[test]
fn wishbone_rtl_loop_monitors() {
    let filename = "../examples/wishbone/wishbone.prot";
    let (symbols, module) = load(filename);
    let mut mutations = 0;
    for transactions in [
        "read_write.tx",
        "4.8_constant_address_burst.tx",
        "4.?_incremental_address_burst.tx",
        "4.?_incremental_address_burst_wrap.tx",
    ] {
        let path = format!("../examples/wishbone/{transactions}");
        let mut handler = DiagnosticHandler::default();
        let traces =
            crate::transaction_frontend(&path, &symbols, &module.protos, &mut handler).unwrap();
        for trace in traces {
            let samples = driver_samples(filename, &trace, |ctx, module| {
                PatronusSim::new_with_context(
                    ctx,
                    &[
                        "../examples/wishbone/rtl/dut.v",
                        "../examples/wishbone/rtl/tb.v",
                    ],
                    Some("tb"),
                    module,
                    None,
                )
                .unwrap()
            });
            assert_eq!(
                monitor_failure(filename, &[], &samples),
                None,
                "{transactions}"
            );
            // Changing a request while waiting must kill the selected burst,
            // even if the changed sample resembles another valid protocol.
            if let Some(cycle) = (1..samples.len()).find(|&cycle| {
                let prev = &samples[cycle - 1];
                let now = &samples[cycle];
                prev["ACK"].to_u64() == Some(0)
                    && now["RST"].to_u64() == Some(0)
                    && now["CYC"].to_u64() == Some(1)
                    && now["STB"].to_u64() == Some(1)
                    && now["WE"].to_u64() == Some(1)
                    && now["CTI"] == prev["CTI"]
                    && matches!(now["CTI"].to_u64(), Some(1 | 2))
            }) {
                for (pin, mask, width) in [("CTI", 7, 3), ("ADR", 4, 32), ("DAT_O", 1, 32)] {
                    let mut broken = samples.clone();
                    let value = broken[cycle][pin].to_u64().unwrap() ^ mask;
                    broken[cycle].insert(pin.into(), BitVecValue::from_u64(value, width));
                    assert_eq!(
                        monitor_failure(filename, &[], &broken),
                        Some(cycle),
                        "{transactions}: {pin}"
                    );
                    mutations += 1;
                }
            }
            if let Some(cycle) = (1..samples.len()).find(|&cycle| {
                samples[cycle - 1]["ACK"].to_u64() == Some(1)
                    && matches!(samples[cycle - 1]["CTI"].to_u64(), Some(1 | 2))
                    && samples[cycle]["STB"].to_u64() == Some(1)
            }) {
                // A new beat may capture new data, but its address must still
                // agree with the transaction's saved base and loop counter.
                let mut broken = samples.clone();
                let address = broken[cycle]["ADR"].to_u64().unwrap() ^ 4;
                broken[cycle].insert("ADR".into(), BitVecValue::from_u64(address, 32));
                assert_eq!(
                    monitor_failure(filename, &[], &broken),
                    Some(cycle),
                    "{transactions}: next address"
                );
            }
        }
    }
    assert!(
        mutations >= 9,
        "exercise all three burst transaction suites"
    );
}

#[test]
fn wishbone_loop_monitor_graphs_stay_compact() {
    use crate::ir::driver_to_monitor::{convert_driver_to_monitor, simplify_monitor};
    use crate::ir::joint_automaton::prepare_joint_protocols;
    for mapping in [
        None,
        Some("antmicro_litex.prot"),
        Some("litex_unittest.prot"),
        Some("wb_stream.prot"),
    ] {
        let mut diagnostics = DiagnosticHandler::default();
        let mapping_path = mapping.map(|p| format!("../examples/wishbone/{p}"));
        let mut paths = vec!["../examples/wishbone/wishbone.prot"];
        paths.extend(mapping_path.as_deref());
        let (mut symbols, modules) = frontend(&paths, &mut diagnostics, false, false).unwrap();
        let mut ctx = Context::default();
        for module in modules {
            if mapping.is_some() && module.name == "Wishbone" {
                continue;
            }
            let drivers = prepare_joint_protocols(&mut ctx, &module.protos, &mut symbols).unwrap();
            for (proto, driver) in module.protos.iter().zip(drivers) {
                let monitor = convert_driver_to_monitor(&mut ctx, driver, &mut symbols).unwrap();
                let monitor = simplify_monitor(&mut ctx, monitor, &mut symbols);
                let dot = monitor.to_dot_string(&ctx, &symbols);
                // DOT expands expressions, so this catches repeated subexpressions
                // growing even when their shared DAG representation remains small.
                assert!(
                    dot.len() < 16 * 1024,
                    "{} monitor expressions grew excessively",
                    proto.name
                );
                assert!(
                    monitor.graph.nodes().count() <= 5,
                    "{} gained redundant control states",
                    proto.name
                );
            }
        }
    }
}

#[test]
fn loop_monitor_empty_suffix_waits_and_wrap() {
    let filename = "../tests/loops/monitor.prot";
    for name in ["plain", "specialized", "minimum", "minimum_plain"] {
        let mut trace = Vec::new();
        for values in [&[][..], &[10][..], &[10, 20, 30][..], &[10; 260][..]] {
            if name.starts_with("minimum") && values.len() < 2 {
                continue;
            }
            trace.push((name.to_string(), vec![sequence(values, 8)]));
        }
        // Reuse the monitor's state slots for different transactions as well
        // as capturing fresh items within each transaction.
        let samples = driver_samples(filename, &trace, mock_dut);
        assert_eq!(monitor_failure(filename, &[name], &samples), None, "{name}");
    }
    let trace = [vec![], vec![10], vec![10, 20]]
        .into_iter()
        .map(|left| {
            (
                "sequential".into(),
                vec![sequence(&left, 8), sequence(&[30, 40], 8)],
            )
        })
        .collect::<Vec<_>>();
    let samples = driver_samples(filename, &trace, mock_dut);
    assert_eq!(monitor_failure(filename, &["sequential"], &samples), None);
}

#[test]
fn repeat_monitors_share_sequence_alternatives() {
    use crate::ir::driver_to_monitor::convert_driver_to_monitor;
    let filename = "../tests/loops/monitor.prot";
    for (name, width) in [("repeat_plain", 64), ("repeat_specialized", 64)] {
        let trace = [0, 1, 3, 260]
            .into_iter()
            .map(|count| (name.to_string(), vec![scalar(count, width)]))
            .collect::<Vec<_>>();
        let samples = driver_samples(filename, &trace, mock_dut);
        assert_eq!(monitor_failure(filename, &[name], &samples), None, "{name}");
        for pin in ["index", "echo", "data"] {
            let mut broken = samples.clone();
            let cycle = if pin == "data" {
                broken.len() - 1 // held assignment after the final suffix
            } else {
                samples
                    .iter()
                    .position(|s| s["index"].to_u64() == Some(1))
                    .unwrap()
            };
            let value = broken[cycle][pin].to_u64().unwrap() ^ 1;
            broken[cycle].insert(pin.into(), BitVecValue::from_u64(value, 8));
            assert_eq!(
                monitor_failure(filename, &[name], &broken),
                Some(cycle),
                "{name}: {pin}"
            );
        }
        // No value/knownness registers are allocated for the dummy length.
        let (mut symbols, module) = load(filename);
        let ast = module.protos.into_iter().find(|p| p.name == name).unwrap();
        let count = ast.args[0].symbol();
        let mut ctx = Context::default();
        let driver = prepared(&mut ctx, &mut symbols, ast);
        let monitor = convert_driver_to_monitor(&mut ctx, driver, &mut symbols).unwrap();
        assert!(!monitor.value_registers.contains_key(&count));
        assert!(!monitor.knownness_registers.contains_key(&count));
    }
    for name in [
        "repeat_literal",
        "repeat_literal_specialized",
        "repeat_zero",
    ] {
        let samples = driver_samples(filename, &[(name.into(), vec![])], mock_dut);
        assert_eq!(monitor_failure(filename, &[name], &samples), None, "{name}");
        if name == "repeat_zero" {
            let mut broken = samples.clone();
            broken[0].insert("flag".into(), BitVecValue::from_u64(0, 2));
            assert_eq!(monitor_failure(filename, &[name], &broken), Some(0));
        } else {
            let mut short = samples.clone();
            short.remove(2);
            assert_eq!(
                monitor_failure(filename, &[name], &short),
                Some(2),
                "short {name}"
            );
            let mut long = samples.clone();
            long.insert(3, samples[2].clone());
            assert_eq!(
                monitor_failure(filename, &[name], &long),
                Some(3),
                "long {name}"
            );
            if name == "repeat_literal_specialized" {
                for cycle in [0, 2] {
                    let mut broken = samples.clone();
                    let flag = if cycle == 0 { 1 } else { 0 };
                    broken[cycle].insert("flag".into(), BitVecValue::from_u64(flag, 2));
                    assert_eq!(monitor_failure(filename, &[name], &broken), Some(cycle));
                }
            }
        }
    }
    for count in [0, 1, 3] {
        for values in [&[][..], &[10][..], &[10, 20, 30][..]] {
            let samples = driver_samples(
                filename,
                &[(
                    "repeat_then_sequence".into(),
                    vec![scalar(count, 64), sequence(values, 8)],
                )],
                mock_dut,
            );
            assert_eq!(
                monitor_failure(filename, &["repeat_then_sequence"], &samples),
                None
            );
        }
    }
}

#[test]
fn loop_monitor_rejects_bad_suffix_hold_and_short_sequence() {
    let filename = "../tests/loops/monitor.prot";
    for name in ["plain", "specialized"] {
        let trace = [(name.to_string(), vec![sequence(&[10, 20, 30], 8)])];
        let samples = driver_samples(filename, &trace, mock_dut);
        // Every noninitial echo is the previous sample's item, including the
        // sample that observes the next item and the final exit sample.
        for cycle in 1..samples.len() {
            let mut broken = samples.clone();
            let value = broken[cycle]["echo"].to_u64().unwrap() ^ 1;
            broken[cycle].insert("echo".into(), BitVecValue::from_u64(value, 8));
            // Wait samples need not check echo; only a suffix does.
            if cycle == samples.len() - 1 || samples[cycle]["data"] != samples[cycle - 1]["data"] {
                assert_eq!(
                    monitor_failure(filename, &[name], &broken),
                    Some(cycle),
                    "{name}"
                );
            }
        }
        let mut broken = samples.clone();
        let cycle = broken.len() - 1;
        broken[cycle].insert("data".into(), BitVecValue::from_u64(99, 8));
        assert_eq!(
            monitor_failure(filename, &[name], &broken),
            Some(cycle),
            "held {name}"
        );
    }
    for (source, target) in [("specialized", "minimum"), ("plain", "minimum_plain")] {
        for values in [&[][..], &[10][..]] {
            let samples = driver_samples(
                filename,
                &[(source.into(), vec![sequence(values, 8)])],
                mock_dut,
            );
            assert!(
                monitor_failure(filename, &[target], &samples).is_some(),
                "short {target}"
            );
        }
    }
}

#[test]
fn loop_assertions_reject_bad_dut_samples() {
    let (mut symbols, module) = load("../tests/loops/loops.prot");
    let ast = module
        .protos
        .iter()
        .find(|p| p.name == "frozen_check")
        .unwrap()
        .clone();
    let mut ctx = Context::default();
    let mut system = mock_dut(&mut ctx, &module).sys;
    let echo = system
        .outputs
        .iter_mut()
        .find(|output| ctx[output.name] == "echo")
        .unwrap();
    echo.expr = ctx.zero(8);
    let mut dut = PatronusSim::from_system(&ctx, system, &module, None).unwrap();
    let graph = prepared(&mut ctx, &mut symbols, ast);
    let result = interpret(
        &ctx,
        &graph,
        &symbols,
        FxHashMap::from_iter([("values", sequence(&[10, 20], 8))]),
        &mut dut,
    );
    assert!(matches!(
        result.failure,
        Some(GraphInterpretFailure {
            kind: GraphInterpretFailureKind::ExternalAssertion,
            cycle: 1,
            ..
        })
    ));
}

#[test]
fn prepared_loop_expressions_stay_compact() {
    use patronus::expr::ForEachChild;
    // Count the expanded expression tree, not unique DAG nodes: duplicated
    // predicates are precisely what made the DOTs and generated formulas grow.
    fn size(ctx: &Context, expr: ExprRef) -> usize {
        let mut total = 1;
        ctx[expr].for_each_child(|child| {
            if total <= 32 {
                total += size(ctx, *child);
            }
        });
        total
    }
    for filename in [
        "../tests/loops/loops.prot",
        "../examples/wishbone/wishbone.prot",
    ] {
        let (symbols, module) = load(filename);
        for ast in module.protos {
            let name = ast.name.clone();
            let mut symbols = symbols.clone();
            let mut ctx = Context::default();
            let graph = prepared(&mut ctx, &mut symbols, ast);
            for node in graph.reachable_node_ids(&ctx, graph.entry) {
                let mut expressions = graph[node]
                    .transitions
                    .iter()
                    .map(|t| t.guard)
                    .collect::<Vec<_>>();
                for action in &graph[node].actions {
                    expressions.push(action.guard);
                    if let Op::Assign(_, assignment) = &graph[action.op] {
                        expressions.push(assignment.dont_care);
                        expressions.extend(
                            assignment
                                .concretes
                                .iter()
                                .flat_map(|&(guard, rhs)| [guard, rhs]),
                        );
                    }
                }
                for expr in expressions {
                    assert!(
                        size(&ctx, expr) <= 32,
                        "{name}: {node}: expression grew: {}",
                        crate::ir::graphviz::format_expr(&ctx, &graph, expr)
                    );
                }
            }
        }
    }
}

#[test]
fn wishbone_pin_history_is_eliminated() {
    let (symbols, module) = load("../examples/wishbone/wishbone.prot");
    for ast in module.protos {
        let mut symbols = symbols.clone();
        let mut ctx = Context::default();
        let name = ast.name.clone();
        let mut graph = lower_ast_to_ir(&mut ctx, ast, &mut symbols);
        contract_edges(&mut ctx, &mut graph, &symbols);
        let entry = graph.entry;
        let initial = insert_assignment_registers(&mut ctx, &mut graph, &mut symbols, entry);
        simplify_assignments(&mut ctx, &mut graph, &symbols, &initial);
        for register in initial.keys() {
            assert!(
                !graph.register_inits.contains_key(register),
                "{name}: pin history {} remains",
                symbols[*register].name()
            );
            assert!(
                graph
                    .reachable_node_ids(&ctx, entry)
                    .iter()
                    .all(|&n| graph[n]
                        .actions
                        .iter()
                        .all(|a| !matches!(graph[a.op], Op::Assign(r, _) if r == *register))),
                "{name}: pin-history update remains"
            );
        }
        if let Some(directory) = std::env::var_os("PROTOCOLS_WISHBONE_DOT_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            normalize_assignments(&mut ctx, &mut graph, &symbols);
            graph.garbage_collect_unreachable(&ctx);
            let dot = crate::ir::graphviz::to_dot_string(&ctx, &graph, &symbols);
            std::fs::write(directory.join(format!("{name}.dot")), dot).unwrap();
        }
    }
}
