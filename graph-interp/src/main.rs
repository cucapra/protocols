mod execution;
mod monitor;

use clap::error::ErrorKind;
use clap::{Parser, ValueEnum};
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::frontend::{Module, require_single_module};
use protocols::{Value, frontend, transaction_frontend};
use std::num::NonZeroUsize;

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum Flow {
    /// Interpret each transaction against its own protocol graph in sequence.
    Sequential,
    /// Build and interpret one deterministic graph for each complete trace.
    TraceGraph,
    /// Lower each complete trace graph to a transition system that is interpreted.
    TraceSystem,
    /// Lower a bounded transaction sequence to a driver transition system that is interpreted.
    BoundedDriver,
    /// Build an unbounded driver transition system.
    UnboundedDriver,
    /// Evaluate a waveform with an unbounded monitor transition system.
    UnboundedMonitor,
}

#[derive(Parser, Debug)]
struct Cli {
    /// Paths to one or more Verilog (.v) files.
    #[arg(long, value_name = "VERILOG_FILES", value_delimiter = ' ', num_args = 1..)]
    verilog: Vec<String>,

    /// One or more protocol files.
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: Vec<String>,

    /// Path to a Transactions (.tx) file.
    #[arg(short, long, value_name = "TRANSACTIONS_FILE")]
    transactions: Option<String>,

    /// Waveform to evaluate with --flow unbounded-monitor.
    #[arg(short, long)]
    wave: Option<String>,

    /// Waveform instances, as instance:Module.
    #[arg(short, long, value_delimiter = ' ', num_args = 1..)]
    instances: Vec<String>,

    #[arg(long)]
    sample_posedge: Option<String>,

    /// Use zero for waveform X/Z values instead of deterministic random values.
    #[arg(long)]
    force_x_to_zero: bool,

    /// Name of the top-level module, if one exists.
    #[arg(short, long, value_name = "MODULE_NAME")]
    module: Option<String>,

    /// Execution and lowering strategy.
    #[arg(long, value_enum)]
    flow: Flow,

    /// Maximum transaction count for the bounded-driver flow.
    #[arg(long, value_name = "TRANSACTIONS")]
    bound: Option<NonZeroUsize>,

    /// Skip static checks for step/fork errors.
    #[arg(long)]
    skip_static_step_fork_checks: bool,

    /// Print the final graph used by the selected flow.
    #[arg(long)]
    graphout: bool,

    /// Print trace status lines and ASCII waveforms.
    #[arg(long)]
    ascii_waveform: bool,

    /// Print reaching-definition analysis results.
    #[arg(long)]
    reaching_definitions: bool,

    /// Print graph-interpreter failures in transition-system short form.
    #[arg(long)]
    brief_graph_errors: bool,
}

fn validate_cli(cli: &Cli) -> Result<(), String> {
    if cli.flow == Flow::UnboundedMonitor {
        if cli.wave.is_none() || cli.instances.is_empty() {
            return Err("--flow unbounded-monitor requires --wave and --instances".to_string());
        }
        if cli.transactions.is_some()
            || !cli.verilog.is_empty()
            || cli.module.is_some()
            || cli.graphout
            || cli.ascii_waveform
        {
            return Err(
                "--flow unbounded-monitor does not accept driver or trace-display arguments"
                    .to_string(),
            );
        }
    } else {
        if cli.transactions.is_none() {
            return Err("driver flows require --transactions".to_string());
        }
        if cli.wave.is_some()
            || !cli.instances.is_empty()
            || cli.sample_posedge.is_some()
            || cli.force_x_to_zero
        {
            return Err("waveform arguments require --flow unbounded-monitor".to_string());
        }
    }
    match (cli.flow, cli.bound) {
        (Flow::BoundedDriver, None) => {
            return Err("--flow bounded-driver requires --bound".to_string());
        }
        (Flow::BoundedDriver, Some(_)) | (_, None) => {}
        (_, Some(_)) => {
            return Err("--bound is only valid with --flow bounded-driver".to_string());
        }
    }

    if cli.ascii_waveform && cli.flow == Flow::Sequential {
        return Err("--ascii-waveform is not supported by --flow sequential".to_string());
    }
    if cli.brief_graph_errors && !matches!(cli.flow, Flow::Sequential | Flow::TraceGraph) {
        return Err("--brief-graph-errors is only valid with graph-interpreter flows".to_string());
    }
    if cli.reaching_definitions && !matches!(cli.flow, Flow::TraceGraph | Flow::TraceSystem) {
        return Err(
            "--reaching-definitions is only valid with --flow trace-graph or trace-system"
                .to_string(),
        );
    }
    Ok(())
}

fn load_protocols(cli: &Cli) -> (SymbolTable, Vec<Module>) {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    frontend(
        &cli.protocol,
        &mut handler,
        cli.skip_static_step_fork_checks,
        false,
    )
    .unwrap()
}

fn load_traces(cli: &Cli, st: &SymbolTable, module: &Module) -> Vec<Vec<(String, Vec<Value>)>> {
    let mut handler = DiagnosticHandler::new(clap::ColorChoice::Never, false, true, false);
    transaction_frontend(
        cli.transactions.as_ref().unwrap(),
        st,
        &module.protos,
        &mut handler,
    )
    .unwrap()
}

fn main() {
    let cli = Cli::parse();
    if let Err(message) = validate_cli(&cli) {
        clap::Error::raw(ErrorKind::ArgumentConflict, message).exit();
    }

    if cli.flow == Flow::UnboundedMonitor {
        match monitor::run(&cli) {
            Ok(failed) => {
                println!("{}", if failed { "Fail" } else { "Pass" });
                std::process::exit(i32::from(failed));
            }
            Err(error) => {
                eprintln!("{error}");
                std::process::exit(2);
            }
        }
    }

    let (st, modules) = load_protocols(&cli);
    let module = require_single_module(modules, &cli.protocol).unwrap();
    let traces = load_traces(&cli, &st, &module);
    execution::run(&cli, &st, &module, &traces);
}
