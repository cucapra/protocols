// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecValue;
use clap::*;
use protocols::backends::{PinAnnotation, to_verilog};
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::{frontend, transaction_frontend};
use std::path::Path;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

    #[command(subcommand)]
    command: Option<Cmds>,
}

#[derive(Subcommand, Debug)]
enum Cmds {
    Verilog {
        verilog_tb: String,
        #[arg(long)]
        transactions: Option<String>,
        #[arg(long)]
        vcd_out: Option<String>,
        #[arg(long)]
        clock: Option<String>,
    },
    RunVerilog {
        run_dir: String,
        #[arg(long)]
        transactions: Option<String>,
        #[arg(long)]
        clock: Option<String>,
        /// Paths to one or more Verilog (.v) files
        #[arg(long, value_name = "VERILOG_FILES", value_delimiter = ' ', num_args = 1..)]
        verilog: Vec<String>,
    },
}

fn load_trace(
    protos: &[(Transaction, SymbolTable)],
    transactions: Option<&str>,
) -> Vec<(String, Vec<BitVecValue>)> {
    if let Some(filename) = transactions {
        let mut d = DiagnosticHandler::new(ColorChoice::Auto, false, true, false);
        let traces = transaction_frontend(filename, protos.iter(), &mut d).unwrap();
        if !traces.is_empty() {
            if traces.len() > 1 {
                log::warn!("More than 1 trace in {filename}. Picking first one.");
            }
            traces.into_iter().next().unwrap()
        } else {
            vec![]
        }
    } else {
        vec![]
    }
}

fn make_verilog_tb(
    protos: &[(Transaction, SymbolTable)],
    verilog_tb: String,
    transactions: Option<String>,
    vcd_out: Option<String>,
    clock: Option<String>,
) {
    let trace = load_trace(protos, transactions.as_deref());
    let mut pins = vec![];
    if let Some(clock) = clock {
        pins.push((clock, PinAnnotation::Clock));
    }
    let out_file = std::fs::File::create(&verilog_tb).unwrap();
    let mut out_writer = std::io::BufWriter::new(out_file);
    let tb_name = "tb";
    to_verilog(
        tb_name,
        protos,
        &pins,
        vcd_out.as_deref(),
        &trace,
        &mut out_writer,
    )
    .unwrap();
}

fn run_verilog_tb(
    protos: &[(Transaction, SymbolTable)],
    run_dir: String,
    transactions: Option<String>,
    clock: Option<String>,
    verilog: Vec<String>,
) {
    // check whether iverilog is available
    let _ = std::process::Command::new("iverilog")
        .arg("-v")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("Could not launch Icarus Verilog (iverilog!)")
        .wait()
        .unwrap();

    // ensure that the run_dir exists
    let cwd = Path::new(&run_dir);
    if !cwd.exists() {
        std::fs::create_dir_all(cwd).unwrap();
    }

    // generate the testbench file
    let abs_cwd = cwd.canonicalize().unwrap();
    let verilog_tb = "tb.v";
    let verilog_tb_str = abs_cwd.join(verilog_tb).to_str().unwrap().to_string();
    let vcd_out_rel = "dump.vcd";
    make_verilog_tb(
        protos,
        verilog_tb_str,
        transactions,
        Some(vcd_out_rel.to_string()),
        clock,
    );

    // check verilog files
    let mut filenames = vec![];
    for filename in verilog.iter() {
        let path = Path::new(filename);
        if !path.exists() {
            panic!("cannot find verilog file {filename}");
        } else {
            let abs_path = path.canonicalize().unwrap();
            filenames.push(abs_path.to_str().unwrap().to_string());
        }
    }

    // run icarus
    let a_out = cwd.join("a.out");
    if a_out.exists() {
        std::fs::remove_file(&a_out).unwrap();
    }
    let _ = std::process::Command::new("iverilog")
        .arg("-g2012")
        .arg(verilog_tb)
        .args(filenames)
        .current_dir(cwd)
        .spawn()
        .expect("Failed to compile testbench with icarus.")
        .wait()
        .unwrap();
    if !a_out.exists() {
        panic!("Icarus did not produce the expected a.out!");
    }

    // run tb
    let _ = std::process::Command::new("./a.out")
        .current_dir(cwd)
        .spawn()
        .expect("Failed to start testbench.")
        .wait()
        .unwrap();
}

fn main() {
    // Parse CLI args
    let args = Args::parse();

    // we always parse and type check the protocol file
    let mut d = DiagnosticHandler::new(ColorChoice::Auto, false, true, false);
    let protos = frontend(args.protocol, &mut d);

    match args.command {
        None => {}
        Some(Cmds::Verilog {
            verilog_tb,
            transactions,
            vcd_out,
            clock,
        }) => {
            make_verilog_tb(&protos, verilog_tb, transactions, vcd_out, clock);
        }
        Some(Cmds::RunVerilog {
            run_dir,
            transactions,
            clock,
            verilog,
        }) => {
            run_verilog_tb(&protos, run_dir, transactions, clock, verilog);
        }
    }
}
