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
use protocols::frontend;
use rustc_hash::{FxHashMap, FxHashSet};

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
    #[arg(short, long, value_delimiter = ' ', num_args = 1..)]
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

    /// This flag will make the bi append any in-progress transactions to the trace.
    #[arg(long)]
    include_in_progress: bool,

    #[arg(long, value_name = "SHOW_START_END_WAVEFORM_TIME_FOR_EACH_TRANSACTION")]
    show_waveform_time: bool,

    #[arg(long, value_name = "TIME_UNIT", requires = "show_waveform_time")]
    time_unit: Option<String>,

    /// Limit the number of traces written to stdout.
    #[arg(long)]
    max_traces: Option<u32>,
}

#[allow(unused_variables)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse CLI args
    let cli = Cli::parse();

    if let Some(tu) = cli.time_unit {
        assert_eq!(tu, "ns", "Only nano seconds are supported");
    }

    // parse protocol file
    let show_warnings = false;
    let skip_static_step_fork_checks = false;
    let mut d = DiagnosticHandler::new(ColorChoice::Auto, false, show_warnings, false);
    let parsed_ir = frontend(cli.protocol, &mut d, skip_static_step_fork_checks)?;

    let designs = find_designs(parsed_ir.iter());

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
            parsed_ir
                .iter()
                .filter(|(t, _)| t.is_idle)
                .map(|(t, _)| t.name.clone()),
        )
    };

    // parse waveform
    let trace = WaveSignalTrace::open(&cli.wave, &designs, &instances, cli.sample_posedge.clone())?;

    let mut bi = BackwardsInterpreter::new(parsed_ir.iter(), trace, 0, cli.include_in_progress);
    let r = bi.run();

    if let BIResult::Fail(failures) = r {
        for (ii, (trace_id, fails)) in failures.into_iter().enumerate() {
            if ii > 0 {
                println!();
            }
            let mut trace = bi.protocol_traces().get_trace(trace_id);
            trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
            print_trace(ii, &trace, cli.show_steps, cli.show_waveform_time, |step| {
                bi.step_to_ns(step)
            });

            for fail in fails {
                let proto = &parsed_ir[fail.proto_id].0;
                let msg = format!(
                    "[{}] executing step {} of the transaction: {} != {}",
                    fail.thread_name,
                    fail.thread_local_step,
                    fail.a.to_hex_str(),
                    fail.b.to_hex_str()
                );
                d.emit_diagnostic_stmt(proto, &fail.stmt, &msg, Level::Error);
            }
        }

        Err("Monitor failed".into())
    } else {
        let unique_traces = bi.protocol_traces().unique_traces();
        let num_traces = unique_traces.len();
        for (ii, mut trace) in unique_traces.into_iter().enumerate() {
            if cli.max_traces == Some(ii as u32) {
                println!("Displayed {}/{} traces.", ii, num_traces);
                break;
            }
            trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
            if ii > 0 {
                println!();
            }
            print_trace(ii, &trace, cli.show_steps, cli.show_waveform_time, |step| {
                bi.step_to_ns(step)
            });
        }
        Ok(())
    }
}

fn print_trace(
    ii: usize,
    trace: &ProtoTrace,
    show_steps: bool,
    show_time: bool,
    get_ns: impl Fn(u32) -> String,
) {
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
            if let Some(end) = end {
                if start == end {
                    println!(" [{start}]");
                } else {
                    println!(" [{start} .. {end}]");
                }
            } else {
                println!(" [{start} .. ]");
            }
        } else if show_time {
            if let Some(end) = end {
                // the original monitor always shows the time of the next time step as end time
                println!("  // [time: {} -> {}]", get_ns(*start), get_ns(*end + 1));
            } else {
                println!("  // [time: {} -> ]", get_ns(*start));
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
