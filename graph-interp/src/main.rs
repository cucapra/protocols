use std::panic::{AssertUnwindSafe, catch_unwind};

use clap::Parser;
use protocols::PatronusSim;
use protocols::frontend::ast::Protocol;
use protocols::frontend::design::find_a_single_design;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::{graph_interpreter};
use protocols::ir::proto_graph::ProtoGraph;
use protocols::ir::lowering::lower_ast_to_ir;
use protocols::{Value, frontend, transaction_frontend};
use rustc_hash::FxHashMap;
use protocols::ir::edge_contract::{contract_edges, normalize_assignments};
use protocols::ir::graphviz::to_dot_string;

#[derive(Parser, Debug)]
struct Cli {
    /// Paths to one or more Verilog (.v) files
    #[arg(long, value_name = "VERILOG_FILES", value_delimiter = ' ', num_args = 1..)]
    verilog: Vec<String>,

    /// Path to a Protocol (.prot) file
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

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

    /// Normalize assignments such that each node assigns every pin
    #[arg(long)]
    normalize_assignments: bool,

    #[arg(long)]
    output_irs: bool,
}

fn load_protocols(cli: &Cli) -> (SymbolTable, Vec<Protocol>) {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    frontend(
        &cli.protocol,
        &mut handler,
        cli.skip_static_step_fork_checks,
    )
    .unwrap()
}

fn load_traces(cli: &Cli, st: &SymbolTable, protos: &[Protocol]) -> Vec<Vec<(String, Vec<Value>)>> {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    transaction_frontend(&cli.transactions, st, protos, &mut handler).unwrap()
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

fn main() {
    let cli = Cli::parse();
    let (st, protos) = load_protocols(&cli);
    let traces = load_traces(&cli, &st, &protos);
    let design = find_a_single_design(&st, &protos, &cli.protocol).unwrap();
    let mut sim = PatronusSim::new(&cli.verilog, cli.module.as_deref(), &design, None).unwrap();

    let mut graphs: Vec<(String, ProtoGraph)> = protos
        .iter()
        .map(|proto| (proto.name.clone(), lower_ast_to_ir(proto.clone(), &st)))
        .collect();

    // edge contract the graphs
    if cli.contract_edges {
        for (_, graph) in &mut graphs {
            contract_edges(graph, &st);
        }
    }

    // normalize assignments - only if we also contract edges
    if cli.contract_edges && cli.normalize_assignments {
        for (_, graph) in &mut graphs {
            normalize_assignments(graph, &st);
        }
    }

    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(|| {
        for (trace_index, trace) in traces.into_iter().enumerate() {
            for (name, values) in trace {
                let (_, pg) = graphs.iter_mut().find(|(n, _)| n == &name)
                    .unwrap_or_else(|| panic!("unknown protocol {name}"));
                let args = build_arg_map(&pg.args, &st, values);
                graph_interpreter::interpret(pg, &st, args, &mut sim);

                if cli.output_irs {
                    println!("{}", to_dot_string(pg, &st));
                }

            }
            println!("trace {} executed successfully", trace_index);
        }
    }));
    std::panic::set_hook(old_hook);

    if let Err(payload) = result {
        print_panic_payload(payload);
        std::process::exit(101);
    }
}
