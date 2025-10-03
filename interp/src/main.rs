// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::collections::HashMap;

use clap::ColorChoice;
use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction, Type};
use protocols::scheduler::Scheduler;
use protocols::setup::{assert_ok, setup_test_environment};
use protocols::transactions_parser::parse_transactions_file;

/// Args for the interpreter CLI
#[derive(Parser, Debug)]
#[command(version, about, long_about = None, disable_version_flag = true)]
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

    /// (Optional) Name of the waveform file (.fst) in which to save results
    #[arg(short, long, value_name = "WAVEFORM_FILE")]
    fst: Option<String>,

    /// Users can specify `-v` or `--verbose` to toggle logging
    #[command(flatten)]
    verbosity: Verbosity<WarnLevel>,

    /// Pass in `--color never` to suppress colored error messages.       
    /// (By default, error messages are displayed w/ ANSI colors.)
    #[arg(long, value_name = "COLOR_CHOICE", default_value = "auto")]
    color: ColorChoice,

    /// Whether to suppress location info (source file and label) in error messages
    #[arg(short, long, value_name = "ERROR_LOCATIONS")]
    no_error_locations: bool,

    /// Stop the interpreter if it ever reaches the maximum number
    /// of cycles specified with this option.
    #[arg(long)]
    max_steps: Option<u32>,
}

/// Examples (enables all tracing logs):
/// ```
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/adders/adder_d1/add_d1.v -p protocols/tests/adders/adder_d1/add_d1.prot -t protocols/tests/adders/adder_d1/both_threads_pass.tx
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/counters/counter.v -p protocols/tests/counters/counter.prot -t protocols/tests/counters/counter.tx -v
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/identities/dual_identity_d1/dual_identity_d1.v -p protocols/tests/identities/dual_identity_d1/dual_identity_d1.prot -t tests/identities/dual_identity_d1/dual_identity_d1.tx
/// ```
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse CLI args
    let cli = Cli::parse();

    let color_choice = cli.color;

    // Set up logger to use the log-level specified via the `-v` flag
    // For concision, we disable timestamps and the module paths in the log
    env_logger::Builder::new()
        .format_timestamp(None)
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    // Create a new handler for dealing with errors/diagnostics
    let protocols_handler = &mut DiagnosticHandler::new(color_choice, cli.no_error_locations);

    // At the moment we only allow the user to specify one Verilog file
    // through the CLI, so we have to wrap it in a singleton Vec
    let (parsed_data, ctx, sys) = setup_test_environment(
        cli.verilog.iter().map(|v| v.as_str()).collect(),
        &cli.protocol,
        cli.module,
        protocols_handler,
    );

    // Nikil says we have to do this step in order to convert
    // `Vec<(Transaction, SymbolTable)>` into `Vec<(&Transaction, &SymbolTable)>`
    let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
        parsed_data.iter().map(|ts| (&ts.0, &ts.1)).collect();

    // Maps a transaction's name to its argument types
    let mut transaction_arg_types: HashMap<String, Vec<Type>> = HashMap::new();
    for (tx, symbol_table) in &transactions_and_symbols {
        transaction_arg_types.insert(tx.name.clone(), tx.get_arg_types(symbol_table));
    }

    // Create a separate `DiagnosticHandler` when parsing the transactions file
    let transactions_handler = &mut DiagnosticHandler::new(color_choice, cli.no_error_locations);
    let todos: Vec<(String, Vec<baa::BitVecValue>)> = parse_transactions_file(
        cli.transactions,
        transactions_handler,
        transaction_arg_types,
    )?;

    // Run the interpreter and the scheduler on the parsed transaction file
    let interpreter = if let Some(waveform_file) = cli.fst {
        patronus::sim::Interpreter::new_with_wavedump(&ctx, &sys, waveform_file)
    } else {
        patronus::sim::Interpreter::new(&ctx, &sys)
    };

    let mut scheduler = Scheduler::new(
        transactions_and_symbols,
        todos,
        &ctx,
        &sys,
        interpreter,
        protocols_handler,
        cli.max_steps.unwrap_or(u32::MAX),
    );
    let results = scheduler.execute_todos();

    // Check whether the protocol was executed successfully
    for res in results {
        assert_ok(&res);
    }
    println!("Protocol executed successfully!");
    Ok(())
}
