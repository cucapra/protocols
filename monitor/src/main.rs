// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod signal_trace;

use crate::signal_trace::{WaveSamplingMode, WaveSignalTrace};
use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{Field, SymbolId, SymbolTable, Transaction, Type};
use protocols::parser::parsing_helper;
use rustc_hash::FxHashMap;

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

    Ok(())
}

/// Concatenates all the names of `struct`s (`Design`s) into one single string
fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<String> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
}

/// Metadata associated with a design (i.e. a `struct` in the Protocols language)
#[allow(dead_code)]
struct Design {
    name: String,
    /// Pins from a struct, along with their associated `SymbolId`s
    pins: Vec<(SymbolId, Field)>,
    symbol: SymbolId,
    /// Index of transactions that use this struct
    /// (e.g. an "Adder" supports these transactions)
    transaction_ids: Vec<usize>,
}

/// Finds all the protocols associated with a given `struct` (called a "design" since its a DUT),
/// returning a `HashMap` from struct names to the actual `Design`
fn find_designs<'a>(
    transactions: impl Iterator<Item = &'a (Transaction, SymbolTable)>,
) -> FxHashMap<String, Design> {
    // Maps the name of the transaction to metadata about the struct (design)
    // We use `FxHashMap` because its a bit faster than the usual `HashMap`
    let mut designs: FxHashMap<String, Design> = FxHashMap::default();
    for (transaction_id, (transaction, symbol_table)) in transactions.enumerate() {
        if let Some(symbol) = transaction.type_param {
            // We assume type parameters have to be structs
            let struct_id = match symbol_table[symbol].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let name = symbol_table[struct_id].name().to_string();
            if let Some(design) = designs.get_mut(&name) {
                design.transaction_ids.push(transaction_id);
            } else {
                // `Field`s are also called `pin`s`
                let pins_vec: Vec<Field> = symbol_table[struct_id].pins().clone();

                // For each pin, look up its associated `SymbolId` in the symbol table
                let pins_with_ids: Vec<(SymbolId, Field)> = pins_vec
                    .into_iter()
                    .map(|pin| {
                        (
                            symbol_table
                                .symbol_id_from_name(pin.name())
                                .expect("Unable to find symbol ID for pin"),
                            pin,
                        )
                    })
                    .collect();
                designs.insert(
                    name.clone(),
                    Design {
                        name,
                        pins: pins_with_ids,
                        symbol,
                        transaction_ids: vec![transaction_id],
                    },
                );
            }
        }
        // skipping any transactions that are not associated with a DUT
    }
    designs
}

struct Instance {
    name: String,
    design: String,
}

/// Takes the contents of the `-i` CLI flag and tries to find
fn parse_instance(duts: &FxHashMap<String, Design>, arg: &str) -> Instance {
    let parts: Vec<&str> = arg.split(':').collect();
    match parts.as_slice() {
        // `module` is the name of the design
        // (In Verilog, "modules" are like interfaces and you have "instances"
        // (concrete instantiations, aka implementations) of the module)
        [inst, module] => {
            if !duts.contains_key(*module) {
                panic!(
                    "Unknown design {module} for instance {inst}. Did you mean {}?",
                    collects_design_names(duts)
                );
            } else {
                Instance {
                    name: inst.to_string(),
                    design: module.to_string(),
                }
            }
        }
        _ => panic!("unexpected instance argument: {arg}"),
    }
}
