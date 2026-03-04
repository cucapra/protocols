// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

pub mod backends;
pub mod design;
pub mod diagnostic;
pub mod errors;
pub mod interpreter;
pub mod ir;
pub mod parser;
pub mod scheduler;
pub mod serialize;
pub mod setup;
pub mod static_checks;
pub mod transactions_parser;
pub mod typecheck;
mod yosys;

/// Simple frontend which loads a single protocols file, type checks and returns the AST.
pub fn frontend(filename: impl AsRef<std::path::Path>) -> Vec<(ir::Transaction, ir::SymbolTable)> {
    // Note: for the monitor, error message locations in `.prot` files are suppressed
    // in the `DiagnosticHandlers` for now
    let mut protocols_handler = default_diagnostics();

    // Parse protocols file
    let transactions_symbol_tables: Vec<(ir::Transaction, ir::SymbolTable)> =
        parser::parse_file(filename, &mut protocols_handler).unwrap();

    // Type-check the parsed transactions
    typecheck::type_check(&transactions_symbol_tables, &mut protocols_handler).unwrap();

    transactions_symbol_tables
}

pub type Traces = Vec<Vec<(String, Vec<baa::BitVecValue>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend<'a>(
    filename: impl AsRef<std::path::Path>,
    protos: impl Iterator<Item = &'a (ir::Transaction, ir::SymbolTable)>,
) -> anyhow::Result<Traces> {
    // Maps a transaction's name to its argument types
    let mut transaction_arg_types = rustc_hash::FxHashMap::default();
    for (tx, symbol_table) in protos {
        transaction_arg_types.insert(tx.name.clone(), tx.get_arg_types(symbol_table));
    }

    // Create a separate `DiagnosticHandler` when parsing the transactions file
    let mut transactions_handler = default_diagnostics();
    transactions_parser::parse_transactions_file(
        filename,
        &mut transactions_handler,
        transaction_arg_types,
    )
}

fn default_diagnostics() -> diagnostic::DiagnosticHandler {
    diagnostic::DiagnosticHandler::new(clap::ColorChoice::Auto, true, false, false)
}
