// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::*;
use protocols::design::find_designs;
use protocols::frontend;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

    #[command(subcommand)]
    command: Option<Cmds>,
}

#[derive(Subcommand, Debug)]
enum Cmds {
    VerilogTb { verilog_tb: String },
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
        Some(Cmds::VerilogTb { verilog_tb }) => {
            // TODO: create verilog tb
        }
    }
}
