// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecValue;
use clap::*;
use protocols::backends::{PinAnnotation, to_verilog};
use protocols::design::find_designs;
use protocols::ir::{SymbolTable, Transaction};
use protocols::{frontend, transaction_frontend};

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
}

fn load_trace(
    transaction_file: Option<&str>,
    protos: &[(Transaction, SymbolTable)],
) -> Vec<(String, Vec<BitVecValue>)> {
    if let Some(filename) = transaction_file {
        let traces = transaction_frontend(filename, protos.iter()).unwrap();
        if traces.len() >= 1 {
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

fn main() {
    // Parse CLI args
    let args = Args::parse();

    // we always parse and type check the protocol file
    let protos = frontend(args.protocol);

    // find module
    let modules = find_designs(protos.iter());
    assert_eq!(
        modules.len(),
        1,
        "Currently we only handle a single modules."
    );
    let (_, module) = modules.into_iter().next().unwrap();

    match args.command {
        None => {}
        Some(Cmds::Verilog {
            verilog_tb,
            transactions,
            vcd_out,
            clock,
        }) => {
            let trace = load_trace(transactions.as_deref(), &protos);
            let mut pins = vec![];
            if let Some(clock) = clock {
                pins.push((clock, PinAnnotation::Clock));
            }
            let out_file = std::fs::File::create(&verilog_tb).unwrap();
            let mut out_writer = std::io::BufWriter::new(out_file);
            to_verilog(
                &verilog_tb,
                &protos,
                &pins,
                vcd_out.as_deref(),
                &trace,
                &mut out_writer,
            )
            .unwrap();
        }
    }
}
