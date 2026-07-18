// Copyright 2025-2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

mod bi;
mod constraints;
mod proto_trace;
mod signal_trace;

use crate::bi::*;
use crate::proto_trace::*;
use crate::signal_trace::*;
use clap::{ColorChoice, Parser};
use clap_verbosity_flag::{Verbosity, WarnLevel};
use protocols::frontend;
use protocols::frontend::Module;
use protocols::frontend::ast::Clock;
use protocols::frontend::diagnostic::{DiagnosticHandler, Level};
use rustc_hash::FxHashSet;

/// Args for the monitor CLI
#[derive(Parser, Debug)]
#[command(version, about, long_about = None, disable_version_flag = true)]
struct Cli {
    #[arg(
        short,
        long,
        value_name = "PROTOCOLS_FILE",
        help = "One or several protocol files."
    )]
    protocol: Vec<String>,

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

    /// To suppress colors in error messages, pass in `--color never`.
    /// Otherwise, by default, error messages are displayed with colors.
    #[arg(long, value_name = "COLOR_CHOICE", default_value = "auto")]
    color: ColorChoice,

    /// If enabled, displays integer literals using hexadecimal notation
    #[arg(short, long, value_name = "DISPLAY_IN_HEX")]
    display_hex: bool,
}

fn get_clock(modules: &[Module], cli_sample_posedge: Option<String>) -> Option<String> {
    let mut clocks: Vec<String> = modules
        .iter()
        .flat_map(|m| match &m.clock {
            Clock::None => None,
            Clock::Posedge(name) => Some(name.to_string()),
        })
        .collect();
    if let Some(name) = cli_sample_posedge {
        clocks.push(name);
    }
    clocks.sort();
    clocks.dedup();
    match clocks.as_slice() {
        [one] => Some(one.clone()),
        [] => None,
        other => {
            eprintln!("Too many clocks: {:?}", other);
            std::process::exit(100);
        }
    }
}

#[allow(unused_variables)]
fn main() {
    // Parse CLI args
    let cli = Cli::parse();

    if let Some(tu) = cli.time_unit {
        assert_eq!(tu, "ns", "Only nano seconds are supported");
    }

    // parse protocol file
    let show_warnings = false;
    let skip_static_step_fork_checks = false;
    let mut d = DiagnosticHandler::new(ColorChoice::Auto, false, show_warnings, false);
    let (st, modules) = frontend(&cli.protocol, &mut d, skip_static_step_fork_checks).unwrap();
    let posedge_clock = get_clock(&modules, cli.sample_posedge);

    // try to find instances that we care about
    if cli.instances.is_empty() {
        println!("Available DUTs are: {}", collects_module_names(&modules));
        println!("No instances specified. Nothing to monitor. Exiting...");
        return;
    }

    let instances: Vec<Instance> = cli
        .instances
        .iter()
        .map(|arg| parse_instance(&modules, arg))
        .collect();

    let bi_protos: Vec<Vec<_>> = instances
        .iter()
        .map(|inst| modules[inst.module_id].protos.clone())
        .collect();

    let mut bis: Vec<_> = instances
        .iter()
        .enumerate()
        .zip(bi_protos.iter())
        .map(|((inst_id, inst), protos)| {
            BackwardsInterpreter::new(&st, protos, inst_id as u32, cli.include_in_progress)
        })
        .collect();

    let step_to_time = {
        // try to parse FST, VCD or GHW file
        if let Ok(mut trace) = WaveSignalTrace::open(&cli.wave, &modules, &instances, posedge_clock)
        {
            run_bis(bis.as_mut_slice(), &mut trace)
        } else {
            // otherwise, we might be dealing with our own custom ASCI format
            let mut trace = AsciWaveTrace::open(&cli.wave, &modules, &instances).unwrap();
            run_bis(bis.as_mut_slice(), &mut trace)
        }
    };

    // display results
    let at_least_one_has_failed = bis.iter().any(|bi| bi.has_failed());
    for (bi, protos) in bis.into_iter().zip(bi_protos) {
        let exclude_from_trace = if cli.include_idle {
            FxHashSet::default()
        } else {
            protos
                .iter()
                .filter(|p| p.is_idle)
                .map(|p| p.name.clone())
                .collect()
        };

        if let Some(failures) = bi.failures() {
            for (ii, (trace_id, fails)) in failures.iter().enumerate() {
                if ii > 0 {
                    println!();
                }
                let mut proto_trace = bi.protocol_traces().get_trace(*trace_id);
                proto_trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
                print_trace(
                    ii,
                    &proto_trace,
                    cli.show_steps,
                    cli.show_waveform_time,
                    cli.display_hex,
                    |step| step_to_time.step_to_ns(step),
                );

                assert!(!fails.is_empty(), "TODO: better failures");

                for fail in fails {
                    let proto = &protos[fail.proto_id];
                    d.emit_diagnostic_stmt(proto, &fail.stmt, &fail.message(), Level::Error);
                }
            }
        } else {
            let unique_traces = bi.protocol_traces().unique_traces();
            let num_traces = unique_traces.len();
            for (ii, mut proto_trace) in unique_traces.into_iter().enumerate() {
                if cli.max_traces == Some(ii as u32) {
                    println!("Displayed {}/{} traces.", ii, num_traces);
                    break;
                }
                proto_trace.retain(|ProtoCall { name, .. }| !exclude_from_trace.contains(name));
                if ii > 0 {
                    println!();
                }
                print_trace(
                    ii,
                    &proto_trace,
                    cli.show_steps,
                    cli.show_waveform_time,
                    cli.display_hex,
                    |step| step_to_time.step_to_ns(step),
                );
            }
        }
    }

    if at_least_one_has_failed {
        std::process::exit(1);
    } else {
        std::process::exit(0);
    }
}

fn run_bis(bis: &mut [BackwardsInterpreter], trace: &mut impl SignalTrace) -> StepToTime {
    loop {
        // step all backwards interpreters that have not failed
        for bi in bis.iter_mut() {
            if !bi.has_failed() {
                let _ = bi.exec_step(trace);
            }
        }
        // step shared trace
        if trace.step() == StepResult::Done {
            break;
        }
    }

    for bi in bis.iter_mut() {
        if !bi.has_failed() {
            bi.finish();
        }
    }

    trace.step_to_time()
}

fn print_trace(
    ii: usize,
    trace: &ProtoTrace,
    show_steps: bool,
    show_time: bool,
    display_hex: bool,
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
                if display_hex {
                    print!("0x{}", v.to_hex_str());
                } else {
                    print!("{}", v.to_dec_str());
                }
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
fn collects_module_names(duts: &[Module]) -> String {
    let mut dut_names: Vec<String> = duts.iter().map(|d| d.name.clone()).collect();
    dut_names.sort();
    dut_names.join(", ")
}

struct Instance {
    name: String,
    #[allow(dead_code)]
    module: String,
    module_id: usize,
}

/// Takes the contents of the `-i` CLI flag and tries to find
fn parse_instance(duts: &[Module], arg: &str) -> Instance {
    let parts: Vec<&str> = arg.split(':').collect();
    match parts.as_slice() {
        // `module` is the name of the design
        // (In Verilog, "modules" are like interfaces and you have "instances"
        // (concrete instantiations, aka implementations) of the module)
        [inst, module] => {
            if let Some(module_id) = duts.iter().position(|d| &d.name == module) {
                Instance {
                    name: inst.to_string(),
                    module: module.to_string(),
                    module_id,
                }
            } else {
                panic!(
                    "Unknown design {module} for instance {inst}. Did you mean {}?",
                    collects_module_names(duts)
                );
            }
        }
        _ => panic!("unexpected instance argument: {arg}"),
    }
}
