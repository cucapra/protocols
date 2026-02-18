// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod axi_experiment;
mod designs;
mod global_context;
mod global_scheduler;
mod interpreter;
mod queue;
mod scheduler;
mod signal_trace;
mod thread;
mod types;

use crate::designs::{Design, Instance, collects_design_names, find_designs, parse_instance};
use crate::global_context::{GlobalContext, TimeUnit};
use crate::global_scheduler::GlobalScheduler;
use crate::scheduler::Scheduler;
use crate::signal_trace::WaveSignalTrace;
use anyhow::{Context, anyhow};
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
    /// Multiple arguments can be passed if they're seperated by whitespace.
    /// Format is: `${instance_name}:${dut_struct_name}`
    #[arg(short, long, value_delimiter = ' ', num_args = 1..)]
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
    /// Note: the full path to the signal should be passed as this argument,
    /// e.g. `uut_rx.clk`, where `uut_rx` is an instance in the signal trace.
    #[arg(long, value_name = "SIGNAL_TO_SAMPLE_ON_RISING_EDGE")]
    sample_posedge: Option<String>,

    /// If enabled, displays the start & end waveform time for each inferred transaction
    #[arg(long, value_name = "SHOW_START_END_WAVEFORM_TIME_FOR_EACH_TRANSACTION")]
    show_waveform_time: bool,

    /// If enabled, displays the thread ID corresponding to each inferred transaction
    #[arg(long, value_name = "SHOW_THREAD_IDS")]
    show_thread_ids: bool,

    /// Specifies the time unit for displaying waveform times.
    /// Can only be used with --show-waveform-time.
    /// Valid options: fs, ps, ns, us, ms, s, auto
    /// Default is 'auto' which selects the unit based on the maximum time in the waveform.
    #[arg(long, value_name = "TIME_UNIT", requires = "show_waveform_time")]
    time_unit: Option<String>,

    /// Optional flag: if enabled, prints the no. of (logical) steps
    /// (i.e. clock cycles) taken by the montior
    #[arg(long, value_name = "PRINT_NUM_STEPS_TAKEN")]
    print_num_steps: bool,

    /// Optional flag: if enabled, always prints out idle transcations
    /// regardless of whether the protocol has been annotated with `#[idle]`
    #[arg(long, value_name = "ALWAYS_PRINT_IDLE_TRANSACTIONS")]
    include_idle: bool,
}

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
    let trace = WaveSignalTrace::open(&cli.wave, &designs, &instances, cli.sample_posedge.clone())
        .with_context(|| format!("failed to read waveform file {}", cli.wave))?;

    // Support multiple structs & designs
    let dut_designs: Vec<&Design> = instances
        .iter()
        .map(|inst| {
            let struct_name = &inst.design_name;
            designs
                .get(struct_name)
                .unwrap_or_else(|| panic!("Missing Design for {}", struct_name))
        })
        .collect();

    // Parse the time unit (defaults to `Auto` if not specified)
    let time_unit = if let Some(ref time_unit_str) = cli.time_unit {
        TimeUnit::from_str(time_unit_str).with_context(|| {
            format!(
                "Invalid time unit: '{}'. Valid options: fs, ps, ns, us, ms, s, auto",
                time_unit_str
            )
        })?
    } else {
        TimeUnit::Auto
    };

    // Check if we have multiple structs/designs

    let multiple_structs = dut_designs.len() > 1;

    // Create a GlobalContext that is shared across all schedulers
    let ctx = GlobalContext::new(&cli, 0, time_unit, multiple_structs);

    // Multi-struct mode: create a GlobalScheduler with one scheduler per design
    let mut schedulers = vec![];

    for design in dut_designs.into_iter() {
        // Filter transactions that belong to this design
        let design_transactions: Vec<(Transaction, SymbolTable)> = design
            .transaction_ids
            .iter()
            .map(|&idx| transactions_symbol_tables[idx].clone())
            .collect();

        if design_transactions.is_empty() {
            continue; // Skip designs with no transactions
        }

        // Create a scheduler for this design, using the design name as the struct name
        let scheduler = Scheduler::initialize(
            design_transactions,
            &ctx,
            &trace,
            design.name.clone(),
            design.symbol_id,
        );

        schedulers.push(scheduler);
    }

    // Create a `GlobalScheduler` whose `schedulers` field
    // contains all the initialized schedulers
    let mut global_scheduler = GlobalScheduler::new(schedulers, trace);

    if let Err(error_msg) = global_scheduler.run(&ctx) {
        eprintln!("{error_msg}");
        return Err(anyhow!("Monitor failed"));
    }

    Ok(())
}
