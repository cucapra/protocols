// Copyright 2025-2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod bi;
mod proto_trace;
mod signal_trace;

use crate::bi::*;
use crate::proto_trace::*;
use crate::signal_trace::*;
use baa::BitVecOps;
use clap::{ColorChoice, Parser};
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::design::{Design, find_designs};
use protocols::diagnostic::{DiagnosticHandler, Level};
use protocols::ir::{SymbolTable, Transaction};
use protocols::parser::parsing_helper;
use rustc_hash::{FxHashMap, FxHashSet};
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

    /// Optional argument which specifies the name of the
    /// signal to sample on a rising edge (posedge). If enabled, this
    /// flag acts as the "clock" signal for the monitor.
    /// Note: the full path to the signal should be passed as this argument,
    /// e.g. `uut_rx.clk`, where `uut_rx` is an instance in the signal trace.
    #[arg(long, value_name = "SIGNAL_TO_SAMPLE_ON_RISING_EDGE")]
    sample_posedge: Option<String>,

    /// Optional flag: if enabled, always prints out idle transcations
    /// regardless of whether the protocol has been annotated with `#[idle]`
    #[arg(long, value_name = "ALWAYS_PRINT_IDLE_TRANSACTIONS")]
    include_idle: bool,

    /// If enabled, displays the start & end step for each inferred transaction
    #[arg(long)]
    show_steps: bool,

    // TODO: we do not actually look at this argument right now
    #[arg(long, value_name = "SHOW_START_END_WAVEFORM_TIME_FOR_EACH_TRANSACTION")]
    show_waveform_time: bool,

    // TODO: we do not actually look at this argument right now
    #[arg(long, value_name = "TIME_UNIT", requires = "show_waveform_time")]
    time_unit: Option<String>,
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
    let mut protocols_handler = DiagnosticHandler::new(ColorChoice::Auto, false, false, false);
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

    let exclude_from_trace = if cli.include_idle {
        FxHashSet::default()
    } else {
        FxHashSet::from_iter(
            transactions_symbol_tables
                .iter()
                .filter(|(t, _)| t.is_idle)
                .map(|(t, _)| t.name.clone()),
        )
    };

    // parse waveform
    let trace = WaveSignalTrace::open(&cli.wave, &designs, &instances, cli.sample_posedge.clone())?;

    let mut bi = BackwardsInterpreter::new(transactions_symbol_tables.iter(), trace, 0);
    let r = bi.run();

    if let BIResult::Fail(failures) = r {
        debug_assert_eq!(
            failures.len(),
            1,
            "TODO: handle multiple possible traces better"
        );
        for (ii, (trace_id, fails)) in failures.into_iter().enumerate() {
            if ii > 0 {
                println!();
            }
            let mut trace = bi.protocol_traces().get_trace(trace_id);
            trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
            print_trace(ii, &trace, cli.show_steps);

            for fail in fails {
                let proto = &transactions_symbol_tables[fail.proto_id].0;
                let msg = format!(
                    "in step {}: [{}] {} != {}",
                    fail.step,
                    fail.thread_name,
                    fail.a.to_hex_str(),
                    fail.b.to_hex_str()
                );
                protocols_handler.emit_diagnostic_stmt(proto, &fail.stmt, &msg, Level::Error);
            }
        }

        Err("".into())
    } else {
        for (ii, mut trace) in bi.protocol_traces().unique_traces().into_iter().enumerate() {
            trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
            print_trace(ii, &trace, cli.show_steps);
        }
        Ok(())
    }
}

fn print_trace(ii: usize, trace: &ProtoTrace, show_steps: bool) {
    println!("// trace {ii}");
    println!("trace {{");
    for ProtoCall {
        name,
        args,
        start,
        end,
    } in trace.iter()
    {
        print!("    {name}(");
        for (ai, arg) in args.iter().enumerate() {
            let is_first = ai == 0;
            if !is_first {
                print!(", ");
            }
            if let Some(v) = arg {
                print!("{}", v.to_dec_str());
            } else {
                print!("X");
            }
        }
        print!(");");
        if show_steps {
            if start == end {
                println!(" [{start}]")
            } else {
                println!(" [{start} .. {end}]");
            }
        } else {
            println!();
        }
    }
    println!("}}");
}

/// Concatenates all the names of `struct`s (`Design`s) into one single string
fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<String> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
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
