use patronus::sim::Interpreter;
use protocols::{
    diagnostic::DiagnosticHandler,
    ir::{SymbolTable, Transaction},
    scheduler::Scheduler,
    setup::{assert_ok, bv, setup_test_environment},
};

fn main() {
    let handler = &mut DiagnosticHandler::new();
    let (parsed_data, ctx, sys) = setup_test_environment(
        "tests/adders/adder_d1/add_d1.v",    // pass in verilog file(s)
        "tests/adders/adder_d1/add_d1.prot", // pass in protocol
        None,                                // list name of top module (if one exists)
        handler,                             // pass handler
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
