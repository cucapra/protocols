use super::{Cli, Flow};
use baa::{BitVecOps, BitVecValue, Value as BaaValue};
use patronus::expr::{Context, ExprRef, TypeCheck};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::TransitionSystem;
use protocols::ascii_waveform::print_ascii_waveform;
use protocols::backends::bmc_transition_system::into_bmc_transition_system;
use protocols::backends::joint_transition_system::into_joint_transition_system;
use protocols::backends::transition_system::into_transition_system;
use protocols::frontend::Module;
use protocols::frontend::ast::Protocol;
use protocols::frontend::symbol::SymbolTable;
use protocols::interpreter::Value as WaveValue;
use protocols::ir::bounded_lowering::lower_bmc;
use protocols::ir::determinize::determinized;
use protocols::ir::edge_contract::contract_edges;
use protocols::ir::graph_interpreter::{self, GraphInterpretFailure, GraphInterpretFailureKind};
use protocols::ir::graphviz::to_dot_string;
use protocols::ir::joint_automaton::ProtocolId;
use protocols::ir::joint_driver::build_joint_driver_automaton;
use protocols::ir::lowering::lower_ast_to_ir;
use protocols::ir::propagate_assigns::{insert_assignment_registers, simplify_assignments};
use protocols::ir::proto_graph::ProtoGraph;
use protocols::ir::reaching_defs::format_reaching_defs;
use protocols::ir::trace_lowering::lower_trace_to_ir;
use protocols::{PatronusSim, PortId, Value};
use rustc_hash::FxHashMap;

type Trace = Vec<(String, Vec<Value>)>;

/// Dispatches execution to the flow selected by the command-line arguments.
pub fn run(cli: &Cli, symbols: &mut SymbolTable, module: &Module, traces: &[Trace]) {
    match cli.flow {
        Flow::Sequential => run_sequential(cli, symbols, module, traces),
        Flow::TraceGraph => run_trace_graph(cli, symbols, module, traces),
        Flow::TraceSystem => run_trace_system(cli, symbols, module, traces),
        Flow::BoundedDriver => run_bounded_driver(
            cli,
            symbols,
            module,
            traces,
            cli.bound.expect("validated bounded-driver bound").get(),
        ),
        Flow::UnboundedDriver => run_unbounded_driver(cli, symbols, module, traces),
        Flow::UnboundedMonitor => unreachable!("waveform monitoring is dispatched separately"),
    }
}

/// Creates a simulator for the DUT described by the command-line arguments.
fn build_dut(ctx: &mut Context, cli: &Cli, module: &Module) -> PatronusSim {
    PatronusSim::new_with_context(ctx, &cli.verilog, cli.module.as_deref(), module, None).unwrap()
}

/// Maps every DUT port to its transition-system expression.
fn dut_port_exprs(dut: &PatronusSim) -> FxHashMap<PortId, ExprRef> {
    dut.ios()
        .filter_map(|port| dut.get_port_expr(port).map(|expr| (port, expr)))
        .collect()
}

/// Indexes the module's protocols by name.
fn protocol_map(module: &Module) -> FxHashMap<&str, &Protocol> {
    module
        .protos
        .iter()
        .map(|protocol| (protocol.name.as_str(), protocol))
        .collect()
}

fn print_trace_success(trace_index: usize) {
    println!("Trace {} executed successfully!", trace_index);
}

fn print_trace_separator(trace_index: usize) {
    if trace_index > 0 {
        println!("\n---\n");
    }
}

/// Prints a graph-interpreter failure in either brief or detailed form.
fn print_graph_failure(failure: &GraphInterpretFailure, brief: bool) {
    let kind = match failure.kind {
        GraphInterpretFailureKind::ExternalAssertion => "Assertion failure",
        GraphInterpretFailureKind::InternalAssertion => "Internal assertion failure",
    };
    if brief {
        println!("{kind} in cycle {}.", failure.cycle);
    } else {
        println!("{kind} in cycle {}: {}", failure.cycle, failure.message);
    }
}

/// Lowers and prepares one trace graph for interpretation or transition-system lowering.
fn prepare_trace_graph(
    ctx: &mut Context,
    cli: &Cli,
    symbols: &mut SymbolTable,
    protocols: &FxHashMap<&str, &Protocol>,
    trace: &Trace,
    trace_index: usize,
) -> ProtoGraph {
    let mut graph = lower_trace_to_ir(ctx, trace, protocols, symbols);
    graph = determinized(ctx, graph, symbols);
    let entry = graph.entry;
    let initial = insert_assignment_registers(ctx, &mut graph, symbols, entry);
    contract_edges(ctx, &mut graph, symbols);
    simplify_assignments(ctx, &mut graph, symbols, &initial);
    let reaching = graph
        .nodes()
        .map(|(id, node)| {
            (
                id,
                node.actions
                    .iter()
                    .filter_map(|a| match &graph[a.op] {
                        protocols::ir::proto_graph::Op::Assign(pin, assignment)
                            if symbols[*pin].is_in_port() =>
                        {
                            Some((symbols[*pin].full_name(symbols), assignment.clone()))
                        }
                        _ => None,
                    })
                    .collect(),
            )
        })
        .collect();
    if cli.reaching_definitions {
        println!("// reaching definitions for trace {trace_index}");
        println!("{}", format_reaching_defs(ctx, &graph, symbols, &reaching));
    }
    if cli.graphout {
        println!("// final trace graph for trace {trace_index}");
        println!("{}", to_dot_string(ctx, &graph, symbols));
    }
    graph
}

/// Executes each protocol instance in a trace sequentially on the DUT.
fn run_sequential(cli: &Cli, symbols: &mut SymbolTable, module: &Module, traces: &[Trace]) {
    let mut ctx = Context::default();
    let graphs: Vec<(String, ProtoGraph)> = module
        .protos
        .iter()
        .map(|protocol| {
            (
                protocol.name.clone(),
                lower_ast_to_ir(&mut ctx, protocol.clone(), symbols),
            )
        })
        .collect();

    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        let mut dut = build_dut(&mut ctx, cli, module);
        let mut failed = false;
        for (name, values) in trace {
            let (_, template) = graphs
                .iter()
                .find(|(protocol_name, _)| protocol_name == name)
                .unwrap_or_else(|| panic!("unknown protocol {name}"));
            let mut graph = template.clone();
            let entry = graph.entry;
            let initial = insert_assignment_registers(&mut ctx, &mut graph, symbols, entry);
            contract_edges(&mut ctx, &mut graph, symbols);
            simplify_assignments(&mut ctx, &mut graph, symbols, &initial);
            if cli.graphout {
                println!("// final graph for protocol {name}");
                println!("{}", to_dot_string(&ctx, &graph, symbols));
            }
            let args: FxHashMap<&str, Value> = graph
                .args
                .iter()
                .zip(values)
                .map(|(arg, value)| (symbols[arg.symbol()].name(), value.clone()))
                .collect();

            let result = graph_interpreter::interpret(&ctx, &graph, symbols, args, &mut dut);
            if let Some(failure) = result.failure {
                print_graph_failure(&failure, cli.brief_graph_errors);
                failed = true;
                break;
            }
        }
        if !failed {
            print_trace_success(trace_index);
        }
    }
}

/// Lowers each trace to a graph and interprets that graph directly.
fn run_trace_graph(cli: &Cli, symbols: &mut SymbolTable, module: &Module, traces: &[Trace]) {
    let protocols = protocol_map(module);
    let mut ctx = Context::default();
    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        let mut dut = build_dut(&mut ctx, cli, module);
        let graph = prepare_trace_graph(&mut ctx, cli, symbols, &protocols, trace, trace_index);
        let result =
            graph_interpreter::interpret(&ctx, &graph, symbols, FxHashMap::default(), &mut dut);
        if let Some(failure) = result.failure {
            print_graph_failure(&failure, cli.brief_graph_errors);
        } else {
            print_trace_success(trace_index);
            if cli.ascii_waveform {
                print_ascii_waveform(
                    result.waveform,
                    |port| dut.port_name(port).to_string(),
                    |port| dut.port_width(port),
                    false,
                );
            }
        }
    }
}

/// Records the current DUT output values in a transition-system waveform.
fn record_transition_waveform(
    waveform: &mut FxHashMap<PortId, Vec<WaveValue>>,
    simulator: &Interpreter,
    dut: &PatronusSim,
    port_expr_refs: &FxHashMap<PortId, ExprRef>,
    is_dont_care: &FxHashMap<PortId, ExprRef>,
) {
    for (port, expr) in port_expr_refs {
        let value = if dut.coi_inputs(*port).any(|input| {
            is_dont_care.get(&input).is_some_and(|is_dont_care| {
                matches!(simulator.get(*is_dont_care), BaaValue::BitVec(value) if value.is_one())
            })
        }) {
            WaveValue::DontCare
        } else {
            match simulator.get(*expr) {
                BaaValue::BitVec(value) => WaveValue::Concrete(value),
                BaaValue::Array(_) => panic!("DUT ports should be bit-vectors"),
            }
        };
        waveform.entry(*port).or_default().push(value);
    }
}

/// Simulates a transition system while invoking a per-cycle input-driving callback.
/// TODO: the amount of arguments to this function is super ugly.
/// TODO: I tried to stick these arguments into a struct,
/// TODO: but that just made the code even uglier.
#[allow(clippy::too_many_arguments)]
fn simulate_transition_system(
    ctx: &Context,
    cli: &Cli,
    trace_index: usize,
    dut: &PatronusSim,
    system: TransitionSystem,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    node_symbol: ExprRef,
    done_state: ExprRef,
    external_assert_state: ExprRef,
    internal_assert_state: ExprRef,
    is_dont_care: FxHashMap<PortId, ExprRef>,
    mut drive_inputs: impl FnMut(&mut Interpreter, usize),
) {
    let mut simulator = Interpreter::new(ctx, &system);
    simulator.init(InitKind::Zero);
    let mut waveform = FxHashMap::default();
    let mut cycle = 0usize;

    loop {
        drive_inputs(&mut simulator, cycle);
        record_transition_waveform(&mut waveform, &simulator, dut, &port_to_expr, &is_dont_care);
        simulator.step();

        let state = simulator.get(node_symbol);
        if state == simulator.get(done_state) {
            for values in waveform.values_mut() {
                values.pop();
            }
            print_trace_success(trace_index);
            break;
        } else if state == simulator.get(external_assert_state) {
            println!("Assertion failure in cycle {}.", cycle);
            break;
        } else if state == simulator.get(internal_assert_state) {
            println!("Internal assertion failure in cycle {}.", cycle);
            break;
        }
        cycle += 1;
    }

    if cli.ascii_waveform {
        print_ascii_waveform(
            waveform,
            |port| dut.port_name(port).to_string(),
            |port| dut.port_width(port),
            false,
        );
    }
}

/// Lowers each trace graph to a transition system and simulates it without extra inputs.
fn run_trace_system(cli: &Cli, symbols: &mut SymbolTable, module: &Module, traces: &[Trace]) {
    let protocols = protocol_map(module);
    let mut ctx = Context::default();
    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        let dut = build_dut(&mut ctx, cli, module);
        let graph = prepare_trace_graph(&mut ctx, cli, symbols, &protocols, trace, trace_index);
        let result = into_transition_system(
            &mut ctx,
            graph,
            dut.sys.clone(),
            dut.port_map.clone(),
            dut_port_exprs(&dut),
            symbols,
        );
        simulate_transition_system(
            &ctx,
            cli,
            trace_index,
            &dut,
            result.ts,
            result.port_to_expr,
            result.node_symbol,
            result.done_state.expect("trace system has a done state"),
            result.external_assert_state,
            result.internal_assert_state,
            result.is_dont_care,
            |_, _| {},
        );
    }
}

/// Builds and simulates a fixed-size, statically allocated driver.
/// we don't need to stream inputs since the bound is known, so every transaction has its own argument slot, so we just initialize all arguments and choices at cycle zero.
fn run_bounded_driver(
    cli: &Cli,
    symbols: &mut SymbolTable,
    module: &Module,
    traces: &[Trace],
    bound: usize,
) {
    let mut ctx = Context::default();
    let protocols = protocol_map(module);
    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        assert!(
            trace.len() <= bound,
            "trace {} contains {} protocol instances but bounded-driver bound is {}",
            trace_index,
            trace.len(),
            bound
        );

        let mut used_names = Vec::new();
        for (name, _) in trace {
            if !used_names.contains(&name.as_str()) {
                used_names.push(name.as_str());
            }
        }
        let used_protocols: Vec<Protocol> = used_names
            .iter()
            .map(|name| protocols[*name].clone())
            .collect();
        let argument_symbols: Vec<_> = used_protocols
            .iter()
            .flat_map(|protocol| protocol.args.iter().map(|argument| argument.symbol()))
            .collect();
        let protocol_indices: FxHashMap<&str, u64> = used_names
            .iter()
            .enumerate()
            .map(|(index, name)| (*name, index as u64))
            .collect();
        let choice_width = if used_names.len() <= 1 {
            1
        } else {
            usize::BITS - (used_names.len() - 1).leading_zeros()
        };

        let dut = build_dut(&mut ctx, cli, module);
        let (mut graph, choices) = lower_bmc(&mut ctx, used_protocols, symbols, bound);
        graph.garbage_collect_unreachable(&ctx);
        graph = determinized(&mut ctx, graph, symbols);
        if cli.graphout {
            println!("{}", to_dot_string(&ctx, &graph, symbols));
        }
        let result = into_bmc_transition_system(
            &mut ctx,
            graph,
            dut.sys.clone(),
            choices,
            dut.port_map.clone(),
            dut_port_exprs(&dut),
            &argument_symbols,
            symbols,
        );
        let protocol_inputs = result.protocol_inputs;
        let protocol_choices = result.protocol_choices;
        simulate_transition_system(
            &ctx,
            cli,
            trace_index,
            &dut,
            result.ts,
            result.port_to_expr,
            result.node_symbol,
            result.done_state.expect("bounded driver has a done state"),
            result.external_assert_state,
            result.internal_assert_state,
            result.is_dont_care,
            |simulator, cycle| {
                if cycle != 0 {
                    return;
                }
                for (instance, (protocol_name, values)) in trace.iter().enumerate() {
                    let protocol = protocols[protocol_name.as_str()];
                    assert_eq!(protocol.args.len(), values.len());
                    for (argument, value) in protocol.args.iter().zip(values) {
                        let input = protocol_inputs[&(instance, argument.symbol())];
                        let value: BitVecValue =
                            value.clone().try_into().expect("value not in bitvec");
                        simulator.set(input, &value);
                    }
                    simulator.set(
                        protocol_choices[instance],
                        &BitVecValue::from_u64(
                            protocol_indices[protocol_name.as_str()],
                            choice_width,
                        ),
                    );
                }
            },
        );
    }
}

/// Builds and simulates the unbounded joint driver automaton.
/// we drive choice-valid, protocol-choice, and arguments when transaction-ready is asserted (in the same cycle)
fn run_unbounded_driver(cli: &Cli, symbols: &mut SymbolTable, module: &Module, traces: &[Trace]) {
    let protocols = protocol_map(module);
    let mut ctx = Context::default();
    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        let mut used_names = Vec::new();
        for (name, _) in trace {
            if !used_names.contains(&name.as_str()) {
                used_names.push(name.as_str());
            }
        }
        let used_protocols: Vec<Protocol> = used_names
            .iter()
            .map(|name| protocols[*name].clone())
            .collect();
        let protocol_indices: FxHashMap<&str, ProtocolId> = used_names
            .iter()
            .enumerate()
            .map(|(index, name)| (*name, index))
            .collect();

        let dut = build_dut(&mut ctx, cli, module);
        let driver = build_joint_driver_automaton(&mut ctx, module, used_protocols, symbols)
            .unwrap_or_else(|error| panic!("failed to build joint driver: {error}"));
        if cli.graphout {
            println!("{}", to_dot_string(&ctx, &driver.graph, symbols));
        }
        let result = into_joint_transition_system(
            &mut ctx,
            driver,
            symbols,
            dut.sys.clone(),
            dut.port_map.clone(),
            dut_port_exprs(&dut),
        );
        let choice_width = result.protocol_choice.get_bv_type(&ctx).unwrap();
        let protocol_inputs = result.protocol_inputs;
        let choice_valid = result.choice_valid;
        let protocol_choice = result.protocol_choice;
        let transaction_ready = result.transaction_ready;
        let mut transaction_index = 0;
        simulate_transition_system(
            &ctx,
            cli,
            trace_index,
            &dut,
            result.ts,
            result.port_to_expr,
            result.node_symbol,
            result.done_state,
            result.external_assert_state,
            result.internal_assert_state,
            result.is_dont_care,
            |simulator, _| {
                let ready = simulator
                    .get(transaction_ready)
                    .try_into_u64()
                    .expect("transaction ready was not a bit-vector")
                    == 1;
                let has_transaction = transaction_index < trace.len();
                simulator.set(
                    choice_valid,
                    &BitVecValue::from_u64(u64::from(ready && has_transaction), 1),
                );
                if !ready || !has_transaction {
                    return;
                }

                let (protocol_name, values) = &trace[transaction_index];
                let protocol_id = protocol_indices[protocol_name.as_str()];
                let protocol = protocols[protocol_name.as_str()];
                assert_eq!(protocol.args.len(), values.len());
                for (argument, value) in protocol.args.iter().zip(values) {
                    let input = protocol_inputs[&(protocol_id, argument.symbol())];
                    let value: BitVecValue = value.clone().try_into().expect("value not in bitvec");
                    simulator.set(input, &value);
                }
                simulator.set(
                    protocol_choice,
                    &BitVecValue::from_u64(protocol_id as u64, choice_width),
                );
                transaction_index += 1;
            },
        );
    }
}
