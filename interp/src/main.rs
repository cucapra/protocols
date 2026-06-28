// Copyright 2025-26 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use clap::{ColorChoice, Parser};
use clap_verbosity_flag::log::LevelFilter;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::ascii_waveform::print_ascii_waveform;
use protocols::frontend::design::find_a_single_design;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::scheduler::Scheduler;
use protocols::{PatronusSim, frontend, transaction_frontend};

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

    /// Determines whether to display bit-vector literal values in
    /// error-messages in hexadecimal
    #[arg(long, value_name = "DISPLAY_IN_HEX")]
    display_hex: bool,

    /// Skips the static checks for step/fork errors.
    #[arg(long)]
    skip_static_step_fork_checks: bool,

    /// Prints only trace status lines and ASCII waveforms
    #[arg(long)]
    ascii_waveform: bool,
}

/// Examples (enables all tracing logs):
/// ```
/// $ cargo run --package protocols-interp -- --verilog tests/adders/adder_d1/add_d1.v -p tests/adders/adder_d1/add_d1.prot -t tests/adders/adder_d1/both_threads_pass.tx
/// $ cargo run --package protocols-interp -- --verilog tests/counters/counter.v -p tests/counters/counter.prot -t tests/counters/counter.tx -v
/// $ cargo run --package protocols-interp -- --verilog tests/identities/dual_identity_d1/dual_identity_d1.v -p tests/identities/dual_identity_d1/dual_identity_d1.prot -t tests/identities/dual_identity_d1/dual_identity_d1.tx
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

fn exit_after_setup_error(error: anyhow::Error, diagnostic_was_emitted: bool) -> ! {
    if !diagnostic_was_emitted {
        eprintln!("Error: {error:#}");
    }
    std::process::exit(1)
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
    let mut protocols_handler = DiagnosticHandler::new(
        color_choice,
        cli.no_error_locations,
        emit_warnings,
        cli.display_hex,
    );

    let (st, protos) = match frontend(
        &cli.protocol,
        &mut protocols_handler,
        cli.skip_static_step_fork_checks,
    ) {
        Ok(result) => result,
        Err(error) => exit_after_setup_error(error, !protocols_handler.error_string().is_empty()),
    };
    let design = find_a_single_design(&st, &protos, &cli.protocol)?;

    // Create a separate `DiagnosticHandler` when parsing the transactions file
    let mut transactions_handler = DiagnosticHandler::new(
        color_choice,
        cli.no_error_locations,
        emit_warnings,
        cli.display_hex,
    );
    let traces =
        match transaction_frontend(cli.transactions, &st, &protos, &mut transactions_handler) {
            Ok(result) => result,
            Err(error) => {
                exit_after_setup_error(error, !transactions_handler.error_string().is_empty())
            }
        };

    let mut any_failed = false;
    for (trace_index, todos) in traces.into_iter().enumerate() {
        if trace_index > 0 {
            println!("\n---\n");
        }

        // Run each trace in isolation with a fresh interpreter and scheduler.
        let waveform_file = cli.fst.as_ref().map(|n| with_trace_suffix(n, trace_index));
        let sim = PatronusSim::new(
            &cli.verilog,
            cli.module.as_deref(),
            &design,
            waveform_file.as_deref(),
        )?;

        let mut scheduler = Scheduler::new(
            &st,
            &protos,
            todos,
            sim,
            &mut protocols_handler,
            cli.max_steps.unwrap_or(u32::MAX),
        );
        let results = scheduler.execute_transactions();
        let trace_failed = results.iter().any(|res| res.is_err());

        if trace_failed {
            any_failed = true;
            println!("Trace {} execution failed.", trace_index);
        } else {
            println!("Trace {} executed successfully!", trace_index);
        }

        if cli.ascii_waveform {
            let wave = scheduler.waveform();
            print_ascii_waveform(
                wave,
                |port| scheduler.port_name(port).to_string(),
                |port| scheduler.port_width(port),
                cli.display_hex,
            );
        }
    }

    if any_failed {
        std::process::exit(101);
    }
    Ok(())
}
