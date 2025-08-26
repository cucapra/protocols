use clap::Parser;
use patronus::sim::Interpreter;
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::scheduler::Scheduler;
use protocols::setup::{assert_ok, bv, setup_test_environment};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to a Verilog file
    #[arg(short, long)]
    verilog_file: String,

    /// Path to a Protocol file
    #[arg(short, long)]
    protocol_file: String,

    /// Name of the top-level module (if one exists)
    toplevel_module_name: Option<String>,
}

fn main() {
    let args = Args::parse();

    // Create a new handler for dealing with errors/diagnostics
    let handler = &mut DiagnosticHandler::new();

    let (parsed_data, ctx, sys) = setup_test_environment(
        &args.verilog_file,
        &args.protocol_file,
        args.toplevel_module_name,
        handler, // pass handler
    );

    // Nikil says we currently have to perform this step in order to parse properly
    let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
        parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

    // CASE 1: BOTH THREADS PASS
    let todos = vec![
        (String::from("add"), vec![bv(1, 32), bv(2, 32), bv(3, 32)]),
        (String::from("add"), vec![bv(4, 32), bv(5, 32), bv(9, 32)]),
    ];

    let sim: &mut Interpreter<'_> = &mut patronus::sim::Interpreter::new(&ctx, &sys);
    let mut scheduler = Scheduler::new(
        transactions_and_symbols.clone(),
        todos.clone(),
        &ctx,
        &sys,
        sim,
        handler,
    );
    let results = scheduler.execute_todos();
    assert_ok(&results[0]);
    assert_ok(&results[1]);
}
