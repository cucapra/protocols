use baa::Value as BaaValue;
use clap::Parser;
use patronus::expr::ExprRef;
use patronus::sim::{InitKind, Interpreter, Simulator};
use protocols::ascii_waveform::print_ascii_waveform;
use protocols::backends::into_transition_system;
use protocols::frontend::ast::{Ast, Protocol};
use protocols::frontend::design::{Design, find_a_single_design};
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::interpreter::Value as WaveValue;
use protocols::ir::determinize::determinized;
use protocols::ir::edge_contract::contract_edges;
use protocols::ir::graph_interpreter;
use protocols::ir::graphviz::to_dot_string;
use protocols::ir::lowering::lower_ast_to_ir;
use protocols::ir::propagate_assigns::propagate_assignments;
use protocols::ir::proto_graph::ProtoGraph;
use protocols::ir::reaching_defs::{format_reaching_defs, reaching_definitions};
use protocols::ir::trace_lowering::lower_trace_to_ir;
use protocols::{PatronusSim, PortId, Value, frontend, transaction_frontend};
use rustc_hash::FxHashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

#[derive(Parser, Debug)]
struct Cli {
    /// Paths to one or more Verilog (.v) files
    #[arg(long, value_name = "VERILOG_FILES", value_delimiter = ' ', num_args = 1..)]
    verilog: Vec<String>,

    #[arg(
        short,
        long,
        value_name = "PROTOCOLS_FILE",
        help = "One or several protocol files."
    )]
    protocol: Vec<String>,

    /// Path to a Transactions (.tx) file
    #[arg(short, long, value_name = "TRANSACTIONS_FILE")]
    transactions: String,

    /// Name of the top-level module (if one exists)
    #[arg(short, long, value_name = "MODULE_NAME")]
    module: Option<String>,

    /// Skips the static checks for step/fork errors.
    #[arg(long)]
    skip_static_step_fork_checks: bool,

    // Contract edges in the graphs such that each edge is a step
    #[arg(long)]
    contract_edges: bool,

    /// Build a big joint ProtoGraph for the input trace
    #[arg(long)]
    respect_forks: bool,

    /// Graphviz DOT to stdout, before interpreting it.
    #[arg(long)]
    graphout: bool,

    /// If passed with --respect-forks, construct a DFA
    #[arg(long)]
    determinize: bool,

    /// Prints trace status lines and ASCII waveforms
    #[arg(long)]
    ascii_waveform: bool,

    /// Print reaching definition analysis results
    #[arg(long)]
    reaching_definitions: bool,

    #[arg(long)]
    transition_system: bool,
}

fn load_protocols(cli: &Cli) -> Ast {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    frontend(
        &cli.protocol,
        &mut handler,
        cli.skip_static_step_fork_checks,
    )
    .unwrap()
}

fn load_traces(cli: &Cli, ast: &Ast) -> Vec<Vec<(String, Vec<Value>)>> {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    transaction_frontend(&cli.transactions, ast, &mut handler).unwrap()
}

fn build_arg_map<'a>(
    args: &'a [protocols::frontend::symbol::Arg],
    symbols: &'a SymbolTable,
    values: Vec<Value>,
) -> FxHashMap<&'a str, Value> {
    assert_eq!(args.len(), values.len(), "argument count mismatch");
    args.iter()
        .zip(values)
        .map(|(arg, value)| (symbols[arg.symbol()].name(), value))
        .collect()
}

fn print_panic_payload(payload: Box<dyn std::any::Any + Send>) {
    if let Some(message) = payload.downcast_ref::<&str>() {
        println!("{message}");
    } else if let Some(message) = payload.downcast_ref::<String>() {
        println!("{message}");
    } else {
        println!("graph interpreter panicked");
    }
}

fn print_trace_success(trace_index: usize) {
    println!("Trace {} executed successfully!", trace_index);
}

fn print_trace_separator(trace_index: usize) {
    if trace_index > 0 {
        println!("\n---\n");
    }
}

fn record_transition_waveform(
    waveform: &mut FxHashMap<PortId, Vec<WaveValue>>,
    sim: &Interpreter,
    port_expr_refs: &FxHashMap<PortId, ExprRef>,
) {
    for (port, expr) in port_expr_refs {
        let value = match sim.get(*expr) {
            BaaValue::BitVec(value) => WaveValue::Concrete(value),
            BaaValue::Array(_) => panic!("DUT ports should be bit-vectors"),
        };
        waveform.entry(*port).or_default().push(value);
    }
}

/// lower each protocol once and interpret every
/// transaction against its own symbolic protocol graph.
fn run_classic(
    cli: &Cli,
    st: &SymbolTable,
    protos: &[Protocol],
    design: &Design,
    traces: Vec<Vec<(String, Vec<Value>)>>,
) {
    let mut graphs: Vec<(String, ProtoGraph)> = protos
        .iter()
        .map(|proto| (proto.name.clone(), lower_ast_to_ir(proto.clone(), st)))
        .collect();

    // edge contract the graphs and normalize assignments
    if cli.contract_edges {
        for (_, graph) in &mut graphs {
            contract_edges(graph, st);

            // if !exists_conflicts(&rd, graph) && all_ports_present(&rd, graph, st) {
            // propagate_assignments(graph, st, &rd);
            // } else {
            //     normalize_assignments(graph, st);
            // }

            if cli.graphout {
                println!("{}", to_dot_string(graph, st).as_str());
            }
        }
    }

    for (trace_index, trace) in traces.into_iter().enumerate() {
        print_trace_separator(trace_index);
        let mut sim = PatronusSim::new(&cli.verilog, cli.module.as_deref(), design, None).unwrap();

        for (name, values) in trace {
            let (_, pg) = graphs
                .iter_mut()
                .find(|(n, _)| n == &name)
                .unwrap_or_else(|| panic!("unknown protocol {name}"));

            let rd = reaching_definitions(pg, st);
            propagate_assignments(pg, st, &rd);

            let args = build_arg_map(&pg.args, st, values);
            graph_interpreter::interpret(pg, st, args, &mut sim);
        }
        print_trace_success(trace_index);
    }
}

/// interpret the entire concrete trace as one big ProtoGraph
fn run_respect_forks(
    cli: &Cli,
    st: &SymbolTable,
    protos: &[Protocol],
    design: &Design,
    traces: &[Vec<(String, Vec<Value>)>],
) {
    let protos_by_name: FxHashMap<&str, &Protocol> =
        protos.iter().map(|p| (p.name.as_str(), p)).collect();

    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        let mut sim = PatronusSim::new(&cli.verilog, cli.module.as_deref(), design, None).unwrap();

        let mut joint = lower_trace_to_ir(trace, &protos_by_name, st, sim.ctx.clone());

        if cli.graphout {
            println!("// joint graph for trace {trace_index}");
            println!("{}", to_dot_string(&joint, st));
        }

        if cli.determinize {
            joint = determinized(joint, st);
        }
        // normalize_assignments(&mut joint, st);

        if cli.graphout {
            println!("// post-determinization joint graph for trace {trace_index}");
            println!("{}", to_dot_string(&joint, st));
        }

        let rd = reaching_definitions(&mut joint, st);
        if cli.reaching_definitions {
            println!("// reaching definitions for trace {trace_index}");
            println!("{}", format_reaching_defs(&joint, st, &rd));
        }

        propagate_assignments(&mut joint, st, &rd);

        if cli.graphout {
            println!("// post-propagation joint graph for trace {trace_index}");
            println!("{}", to_dot_string(&joint, st));
        }

        // args are baked into the graph as constants, so we just pass in an empty map here
        let waveform = graph_interpreter::interpret(&joint, st, FxHashMap::default(), &mut sim);
        if cli.ascii_waveform {
            print_trace_success(trace_index);
            // println!("ascii");
            print_ascii_waveform(
                waveform,
                |port| sim.port_name(port).to_string(),
                |port| sim.port_width(port),
                false,
            );
        } else {
            print_trace_success(trace_index);
        }
    }
}

fn run_transition_system(
    cli: &Cli,
    st: &SymbolTable,
    protos: &[Protocol],
    design: &Design,
    traces: &[Vec<(String, Vec<Value>)>],
) {
    // TODO: Duplicate lowering process as respect forks
    let protos_by_name: FxHashMap<&str, &Protocol> =
        protos.iter().map(|p| (p.name.as_str(), p)).collect();

    for (trace_index, trace) in traces.iter().enumerate() {
        print_trace_separator(trace_index);
        // jankily reuse the sim to get all the stuff we need
        let sim = PatronusSim::new(&cli.verilog, cli.module.as_deref(), design, None).unwrap();
        let sys = sim.sys.clone();
        let port_map = sim.port_map.clone();
        let port_expr_refs: FxHashMap<PortId, ExprRef> = FxHashMap::from_iter(
            sim.ios()
                .filter_map(|port| sim.get_port_expr(port).map(|expr| (port, expr))),
        );

        let mut joint = lower_trace_to_ir(trace, &protos_by_name, st, sim.ctx.clone());
        joint = determinized(joint, st);
        let rd = reaching_definitions(&mut joint, st);
        propagate_assignments(&mut joint, st, &rd);

        // TODO: This is totally stupid
        let res = into_transition_system(joint, sys, port_map, port_expr_refs, st);

        let mut transition_sim = Interpreter::new(&res.ctx, &res.ts);
        transition_sim.init(InitKind::Random(0));
        let mut waveform = FxHashMap::default();
        loop {
            record_transition_waveform(&mut waveform, &transition_sim, &res.port_to_expr);
            transition_sim.step();

            let state = transition_sim.get(res.node_symbol);
            // println!("{:?}", state);
            if state == transition_sim.get(res.done_state.unwrap()) {
                print_trace_success(trace_index);
                break;
            } else if state == transition_sim.get(res.external_assert_state) {
                println!("Assertion failure.");
                break;
            } else if state == transition_sim.get(res.internal_assert_state) {
                println!("Internal assertion failure.");
                break;
            }
        }

        if cli.ascii_waveform {
            print_ascii_waveform(
                waveform,
                |port| sim.port_name(port).to_string(),
                |port| sim.port_width(port),
                false,
            );
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let ast = load_protocols(&cli);
    let st = &ast.st;
    let traces = load_traces(&cli, &ast);
    let design = find_a_single_design(&ast, &cli.protocol).unwrap();

    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(|| {
        if cli.transition_system {
            run_transition_system(&cli, st, &ast.protos, &design, &traces);
        } else if cli.respect_forks {
            run_respect_forks(&cli, st, &ast.protos, &design, &traces);
        } else {
            run_classic(&cli, st, &ast.protos, &design, traces);
        }
    }));
    std::panic::set_hook(old_hook);

    if let Err(payload) = result {
        print_panic_payload(payload);
        std::process::exit(101);
    }
}
