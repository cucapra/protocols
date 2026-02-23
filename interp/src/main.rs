// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use clap::ColorChoice;
use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel, log::LevelFilter};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::scheduler::Scheduler;
use protocols::setup::setup_test_environment;
use protocols::transactions_parser::parse_transactions_file;
use protocols::typecheck::type_check;
use rustc_hash::FxHashMap;

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

    /// Mark this test as allowed to fail (ignored by interpreter, used by test harness)
    #[arg(long)]
    allow_round_trip_failure: bool,
}

/// Examples (enables all tracing logs):
/// ```
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/adders/adder_d1/add_d1.v -p protocols/tests/adders/adder_d1/add_d1.prot -t protocols/tests/adders/adder_d1/both_threads_pass.tx
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/counters/counter.v -p protocols/tests/counters/counter.prot -t protocols/tests/counters/counter.tx -v
/// $ cargo run --package protocols-interp -- --verilog protocols/tests/identities/dual_identity_d1/dual_identity_d1.v -p protocols/tests/identities/dual_identity_d1/dual_identity_d1.prot -t tests/identities/dual_identity_d1/dual_identity_d1.tx
/// ```
fn with_trace_suffix(path: &str, trace_index: usize) -> String {
    let path = std::path::Path::new(path);
    let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    let ext = path.extension().and_then(|e| e.to_str());

    let file_name = if stem.is_empty() {
        if let Some(ext) = ext {
            format!("trace_{}.{}", trace_index, ext)
        } else {
            format!("trace_{}", trace_index)
        }
    } else if let Some(ext) = ext {
        format!("{}_{}.{}", stem, trace_index, ext)
    } else {
        format!("{}_{}", stem, trace_index)
    };

    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => {
            parent.join(file_name).to_string_lossy().to_string()
        }
        _ => file_name,
    }
}

fn main() -> anyhow::Result<()> {
    // Parse CLI args
    let cli = Cli::parse();

    let color_choice = cli.color;

    // Set up logger to use the log-level specified via the `-v` flag
    // For concision, we disable timestamps and the module paths in the log
    env_logger::Builder::new()
        .format_timestamp(None)
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    // Print warning messages only if `--verbose` is enabled
    // (the --verbose flag triggers `LevelFilter::Info`)
    let emit_warnings = cli.verbosity.log_level_filter() == LevelFilter::Info;
    let protocols_handler =
        &mut DiagnosticHandler::new(color_choice, cli.no_error_locations, emit_warnings);

    // At the moment we only allow the user to specify one Verilog file
    // through the CLI, so we have to wrap it in a singleton Vec
    let (parsed_data, ctx, sys) = setup_test_environment(
        cli.verilog.iter().map(|v| v.as_str()).collect(),
        &cli.protocol,
        cli.module,
        protocols_handler,
    );

    // Type-check the parsed transactions
    type_check(&parsed_data, protocols_handler)?;

    // Nikil says we have to do this step in order to convert
    // `Vec<(Transaction, SymbolTable)>` into `Vec<(&Transaction, &SymbolTable)>`
    let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
        parsed_data.iter().map(|ts| (&ts.0, &ts.1)).collect();

    // Maps a transaction's name to its argument types
    let mut transaction_arg_types = FxHashMap::default();
    for (tx, symbol_table) in &transactions_and_symbols {
        transaction_arg_types.insert(tx.name.clone(), tx.get_arg_types(symbol_table));
    }

    // Create a separate `DiagnosticHandler` when parsing the transactions file
    let transactions_handler =
        &mut DiagnosticHandler::new(color_choice, cli.no_error_locations, emit_warnings);
    let traces: Vec<Vec<(String, Vec<baa::BitVecValue>)>> = parse_transactions_file(
        cli.transactions,
        transactions_handler,
        transaction_arg_types,
    )?;

    let mut any_failed = false;
    for (trace_index, todos) in traces.into_iter().enumerate() {
        if trace_index > 0 {
            println!("\n---\n");
        }

        // Run each trace in isolation with a fresh interpreter and scheduler.
        let interpreter = if let Some(waveform_file) = &cli.fst {
            let waveform_file = with_trace_suffix(waveform_file, trace_index);
            patronus::sim::Interpreter::new_with_wavedump(&ctx, &sys, waveform_file)
        } else {
            patronus::sim::Interpreter::new(&ctx, &sys)
        };

        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos,
            &ctx,
            &sys,
            interpreter,
            protocols_handler,
            cli.max_steps.unwrap_or(u32::MAX),
        );
        let results = scheduler.execute_todos();
        let trace_failed = results.iter().any(|res| res.is_err());

        if trace_failed {
            any_failed = true;
            println!("Trace {} execution failed.", trace_index);
        } else {
            println!("Trace {} executed successfully!", trace_index);
        }
    }

    if any_failed {
        panic!("One or more traces failed.");
    }
    Ok(())
}
