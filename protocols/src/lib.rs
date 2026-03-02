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
    let mut protocols_handler = diagnostic::DiagnosticHandler::new(clap::ColorChoice::Auto, true, false, false);

    // Parse protocols file
    let transactions_symbol_tables: Vec<(ir::Transaction,ir:: SymbolTable)> =
        parser::parse_file(filename, &mut protocols_handler).unwrap();

    // Type-check the parsed transactions
    typecheck::type_check(&transactions_symbol_tables, &mut protocols_handler).unwrap();

    transactions_symbol_tables
}