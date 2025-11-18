// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod designs;
mod global_context;
mod interpreter;
mod scheduler;
mod signal_trace;
mod thread;

use crate::designs::{collects_design_names, find_designs, parse_instance, Instance};
use crate::global_context::GlobalContext;
use crate::scheduler::Scheduler;
use crate::signal_trace::WaveSignalTrace;
use anyhow::Context;
use clap::{ColorChoice, Parser};
use clap_verbosity_flag::{Verbosity, WarnLevel};
use log::LevelFilter;
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::parser::parsing_helper;
use protocols::typecheck::type_check;

// From the top-level directory, run:
// $ cargo run --package protocols-monitor -- -p protocols/tests/adders/adder_d1/add_d1.prot -w trace.fst -i add_d1:Adder

/// Args for the monitor CLI
#[derive(Parser, Debug)]
#[command(version, about, long_about = None, disable_version_flag = true)]
struct Cli {
    /// Path to a Protocol (.prot) file
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

    /// Path to a waveform trace (.fst, .vcd, .ghw) file
    #[arg(short, long, value_name = "WAVE_FILE")]
    wave: String,

    /// A mapping of DUT struct in the protocol file to an instance in the signal trace.
    /// Can be used multiple times. Format is: `${instance_name}:${dut_struct_name}
    #[arg(short, long)]
    instances: Vec<String>,

    /// Users can specify `-v` or `--verbose` to toggle logging
    #[command(flatten)]
    verbosity: Verbosity<WarnLevel>,

    /// To suppress colors in error messages, pass in `--color never`
    /// Otherwise, by default, error messages are displayed w/ ANSI colors
    #[arg(long, value_name = "COLOR_CHOICE", default_value = "auto")]
    color: ColorChoice,

    /// If enabled, displays integer literals using hexadecimal notation
    #[arg(short, long, value_name = "DISPLAY_IN_HEX")]
    display_hex: bool,

    /// Optional argument which specifies the name of the
    /// signal to sample on a rising edge (posedge). If enabled, this
    /// flag acts as the "clock" signal for the monitor.
    #[arg(long, value_name = "SIGNAL_TO_SAMPLE_ON_RISING_EDGE")]
    sample_posedge: Option<String>,
}

#[allow(unused_variables)]
fn main() -> anyhow::Result<()> {
    // Parse CLI args
    let cli = Cli::parse();

    // Set up logger to use the log-level specified via the `-v` flag
    // For concision, we disable timestamps and the module paths in the log
    let mut logger = env_logger::Builder::new();

    logger
        .format_timestamp(None)
        .filter_level(cli.verbosity.log_level_filter());

    if cli.color == ColorChoice::Never {
        logger.write_style(env_logger::WriteStyle::Never);
    }

    logger.init();

    // Print warning messages only if `--verbose` is enabled
    // (the --verbose flag triggers `LevelFilter::Info`)
    let emit_warnings = cli.verbosity.log_level_filter() == LevelFilter::Info;

    // Note: for the monitor, error message locations in `.prot` files are suppressed
    // in the `DiagnosticHandlers` for now
    let mut protocols_handler = DiagnosticHandler::new(cli.color, false, emit_warnings);

    // Parse protocols file
    let transactions_symbol_tables: Vec<(Transaction, SymbolTable)> =
        parsing_helper(&cli.protocol, &mut protocols_handler);

    // Type-check the parsed transactions
    type_check(&transactions_symbol_tables, &mut protocols_handler)?;

    let designs = find_designs(transactions_symbol_tables.iter());

    // Try to find instances that we care about
    if cli.instances.is_empty() {
        println!("Available DUTs are: {}", collects_design_names(&designs));
        println!("No instances specified. Nothing to monitor. Exiting...");
        return Ok(());
    }

    let instances: Vec<Instance> = cli
        .instances
        .iter()
        .map(|arg| parse_instance(&designs, arg))
        .collect();

    // parse waveform
    let trace = WaveSignalTrace::open(&cli.wave, &designs, &instances, cli.sample_posedge)
        .with_context(|| format!("failed to read waveform file {}", cli.wave))?;

    // TODO: figure out how to avoid hard-coding this
    let dut_struct_name = &instances[0].design_name;
    let design = designs
        .get(dut_struct_name)
        .with_context(|| format!("Missing Design for {}", dut_struct_name))?;

    // Initialize the `GlobalContext` (shared across all threads)
    // & the scheduler
    let ctx = GlobalContext::new(trace, design.clone(), cli.display_hex);
    let mut scheduler = Scheduler::initialize(transactions_symbol_tables, ctx);

    // Actually run the scheduler
    scheduler.run()
}
