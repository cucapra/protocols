use std::panic::{AssertUnwindSafe, catch_unwind};

use clap::Parser;
use protocols::frontend::ast::Protocol;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::graph_interpreter;
use protocols::ir::lowering::lower_ast_to_ir;
use protocols::setup::create_sim_context;
use protocols::{Value, frontend, transaction_frontend};
use rustc_hash::FxHashMap;

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
}

fn load_protocols(cli: &Cli) -> Vec<(Protocol, SymbolTable)> {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    frontend(
        &cli.protocol,
        &mut handler,
        cli.skip_static_step_fork_checks,
    )
    .unwrap()
}

fn load_traces(cli: &Cli, protos: &[(Protocol, SymbolTable)]) -> Vec<Vec<(String, Vec<Value>)>> {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    transaction_frontend(&cli.transactions, protos.iter(), &mut handler).unwrap()
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
        eprintln!("{message}");
    } else if let Some(message) = payload.downcast_ref::<String>() {
        eprintln!("{message}");
    } else {
        eprintln!("graph interpreter panicked");
    }
}

fn main() {
    let cli = Cli::parse();
    let protos = load_protocols(&cli);
    let traces = load_traces(&cli, &protos);
    let (ctx, sys) = create_sim_context(
        cli.verilog.iter().map(|v| v.as_str()).collect(),
        cli.module.clone(),
    );

    let graphs: FxHashMap<String, _> = protos
        .iter()
        .map(|(proto, symbols)| {
            (
                proto.name.clone(),
                (lower_ast_to_ir(proto.clone()), symbols),
            )
        })
        .collect();

    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(|| {
        for (trace_index, trace) in traces.into_iter().enumerate() {
            for (name, values) in trace {
                let (graph, symbols) = graphs
                    .get(&name)
                    .unwrap_or_else(|| panic!("unknown protocol {name}"));
                let args = build_arg_map(&graph.args, symbols, values);
                graph_interpreter::interpret(
                    graph,
                    symbols,
                    args,
                    &ctx,
                    &sys,
                    // note that this creates a new interpreter for every transaction (even within one trace)
                    // this might not be correct, but we will figure this out once we start working with supporting forks/multi-trace/multi-protocol
                    // transactions
                    patronus::sim::Interpreter::new(&ctx, &sys),
                );
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
