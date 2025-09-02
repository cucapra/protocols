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
use std::panic::panic_any;

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
    /// Can we used multiple times. Format is: `${instance_name}:${dut_struct_name}
    #[arg(short, long)]
    instances: Vec<String>,

    /// Users can specify `-v` or `--verbose` to toggle logging
    #[command(flatten)]
    verbosity: Verbosity<WarnLevel>,
}

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
    let mut protocols_handler = DiagnosticHandler::new();
    let parsed = parsing_helper(&cli.protocol, &mut protocols_handler);

    let designs = find_designs(parsed.iter());

    // try to find instances that we care about
    if cli.instances.is_empty() {
        println!("Available DUTs are: {}", collects_design_names(&designs));
        println!("No instances specified. Nothing to monitor. Exiting...");
        return Ok(());
    }

    let instances: Vec<_> = cli
        .instances
        .iter()
        .map(|arg| parse_instance(&designs, arg))
        .collect();

    // parse waveform
    let mut trace =
        WaveSignalTrace::open(&cli.wave, WaveSamplingMode::Direct, &designs, &instances)
            .expect("failed to read waveform file");

    Ok(())
}

fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<_> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
}

struct Design {
    name: String,
    pins: Vec<Field>,
    symbol: SymbolId,
    transaction_ids: Vec<usize>,
}

fn find_designs<'a>(
    transactions: impl Iterator<Item = &'a (Transaction, SymbolTable)>,
) -> FxHashMap<String, Design> {
    let mut out: FxHashMap<String, Design> = FxHashMap::default();
    for (tran_id, (tran, sym)) in transactions.enumerate() {
        if let Some(symbol) = tran.type_param {
            let struct_id = match sym[symbol].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let name = sym[struct_id].name().to_string();
            if let Some(design) = out.get_mut(&name) {
                design.transaction_ids.push(tran_id);
            } else {
                let pins = sym[struct_id].pins().clone();
                out.insert(
                    name.clone(),
                    Design {
                        name,
                        pins,
                        symbol,
                        transaction_ids: vec![tran_id],
                    },
                );
            }
        }
        // skipping any transactions that are not associated with a DUT
    }
    out
}

struct Instance {
    name: String,
    design: String,
}

fn parse_instance(duts: &FxHashMap<String, Design>, arg: &str) -> Instance {
    let parts: Vec<_> = arg.split(':').collect();
    match parts.as_slice() {
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
