// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod designs;
mod mini_interp;
mod signal_trace;

use crate::designs::{collects_design_names, find_designs, parse_instance, Instance};
use crate::mini_interp::MiniInterpreter;
use crate::signal_trace::{PortKey, SignalTrace, WaveSamplingMode, WaveSignalTrace};
use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::parser::parsing_helper;

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
}

#[allow(unused_variables)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse CLI args
    let cli = Cli::parse();

    // Set up logger to use the log-level specified via the `-v` flag
    // For concision, we disable timestamps and the module paths in the log
    env_logger::Builder::new()
        .format_timestamp(None)
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    // parse protocol file
    let mut protocols_handler = DiagnosticHandler::default();
    let transactions_symbol_tables: Vec<(Transaction, SymbolTable)> =
        parsing_helper(&cli.protocol, &mut protocols_handler);

    let designs = find_designs(transactions_symbol_tables.iter());

    // try to find instances that we care about
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
    let trace = WaveSignalTrace::open(&cli.wave, WaveSamplingMode::Direct, &designs, &instances)
        .expect("failed to read waveform file");

    println!("Success!");

    // TODO: figure out how to avoid hard-coding this
    let design = designs.get("Adder").expect("Missing Design for Adder");
    println!("{:?}", design);

    // TODO: we assume only one `Transaction` & `SymbolTable` for now
    let (transaction, symbol_table) = &transactions_symbol_tables[0];

    // Create a new Interpreter for the `.prot` file
    let mut interpreter = MiniInterpreter::new(transaction, symbol_table);

    for port_key in trace.port_map.keys() {
        // We assume that there is only one `Instance` at the moment
        let PortKey {
            instance_id,
            pin_id,
        } = port_key;

        // Fetch the current value of the `pin_id`
        // (along with the name of the corresponding `Field`)
        let current_value = trace.get(*instance_id, *pin_id);
        let field_name = design
            .get_pin_name(pin_id)
            .unwrap_or_else(|| panic!("Missing pin_id {} in design.pins", pin_id));
        println!(
            "{} ({}) |-> {:#?} ",
            field_name,
            pin_id,
            current_value.clone()
        );

        // TODO: figure out what to do if the `pin_id` already has a value in the environment

        // TODO: figure out how to handle `step()`

        // Update the `args_mapping` with the `current_value` for the `pin_id`
        interpreter.update_arg_value(*pin_id, current_value);
    }

    Ok(())
}
