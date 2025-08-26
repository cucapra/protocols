use clap::Parser;
use clap_verbosity_flag::Verbosity;
use patronus::sim::Interpreter;
use protocols::diagnostic::DiagnosticHandler;
use protocols::ir::{SymbolTable, Transaction};
use protocols::scheduler::Scheduler;
use protocols::setup::{assert_ok, bv, setup_test_environment};

/// Args for the interpreter CLI
#[derive(Parser, Debug)]
#[command(version, about, long_about = None, disable_version_flag = true)]
struct Cli {
    /// Path to a Verilog file
    /// (we give this argument an alias of `-l`
    /// since by default the `verbosity` flag has alias `-v`)
    #[arg(short = 'l', long, value_name = "VERILOG_FILE")]
    verilog: String,

    /// Path to a Protocol file
    #[arg(short, long, value_name = "PROTOCOLS_FILE")]
    protocol: String,

    /// Name of the top-level module (if one exists)
    #[arg(short, long, value_name = "MODULE_NAME")]
    module: Option<String>,

    #[command(flatten)]
    verbosity: Verbosity,
}

/// Example:
/// `cargo run -- -l tests/adders/adder_d1/add_d1.v -p "tests/adders/adder_d1/add_d1.prot"`
fn main() {
    // Parse CLI args
    let cli = Cli::parse();
    env_logger::Builder::new()
        .filter_level(cli.verbosity.log_level_filter())
        .init();

    // Create a new handler for dealing with errors/diagnostics
    let handler = &mut DiagnosticHandler::new();

    let (parsed_data, ctx, sys) = setup_test_environment(
        &cli.verilog,
        &cli.protocol,
        cli.module,
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
