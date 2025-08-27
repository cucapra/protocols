// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::scheduler::Scheduler;
use protocols::setup::{assert_ok, bv, setup_test_environment};

/// Args for the interpreter CLI
#[derive(Parser, Debug)]
#[command(version, about, long_about = None, disable_version_flag = true)]
struct Cli {
    /// Path to a Verilog file
    #[arg(long, value_name = "VERILOG_FILE")]
    verilog: String,

    /// Path to a Protocol file
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

    /// Name of the top-level module (if one exists)
    #[arg(short, long, value_name = "MODULE_NAME")]
    module: Option<String>,

    /// Users can specify `-v` or `--verbose` to toggle logging
    #[command(flatten)]
    verbosity: Verbosity<WarnLevel>,
}

/// Example (enables all tracing logs):
/// `cargo run -- --verilog tests/adders/adder_d1/add_d1.v -p "tests/adders/adder_d1/add_d1.prot" -v`
fn main() {
    // Parse CLI args
    let cli = Cli::parse();

    // Set up logger to use the log-level specified via the `-v` flag
    // For concision, we disable timestamps and the module paths in the log
    env_logger::Builder::new()
        .format_timestamp(None)
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    // Create a new handler for dealing with errors/diagnostics
    let handler = &mut DiagnosticHandler::new();

    let (parsed_data, ctx, sys) =
        setup_test_environment(&cli.verilog, &cli.protocol, cli.module, handler);

    // Nikil says we currently have to perform this step in order to parse properly
    let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
        parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

    // CASE 1: BOTH THREADS PASS
    // TODO: move the todos to a separate file and write a parser to parse the todos
    let todos = vec![
        (String::from("add"), vec![bv(1, 32), bv(2, 32), bv(3, 32)]),
        (String::from("add"), vec![bv(4, 32), bv(5, 32), bv(9, 32)]),
    ];

    let interpreter = patronus::sim::Interpreter::new_with_wavedump(&ctx, &sys, "trace.fst");
    let mut scheduler = Scheduler::new(
        transactions_and_symbols.clone(),
        todos.clone(),
        &ctx,
        &sys,
        interpreter,
        handler,
    );
    let results = scheduler.execute_todos();
    assert_ok(&results[0]);
    assert_ok(&results[1]);
}
