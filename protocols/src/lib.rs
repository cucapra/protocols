// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::diagnostic::DiagnosticHandler;
use anyhow::anyhow;

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
mod static_fork_step_check;
pub mod transactions_parser;
pub mod typecheck;
mod yosys;

/// Simple frontend which loads a single protocols file, type checks and returns the AST.
pub fn frontend(
    filename: impl AsRef<std::path::Path>,
    diag: &mut DiagnosticHandler,
    skip_static_step_fork_checks: bool,
) -> anyhow::Result<Vec<(ir::Transaction, ir::SymbolTable)>> {
    // Parse protocols file
    let transactions_symbol_tables: Vec<(ir::Transaction, ir::SymbolTable)> =
        parser::parse_file(filename, diag).map_err(|e| anyhow!(e))?;

    // Type-check the parsed transactions
    typecheck::type_check(&transactions_symbol_tables, diag)?;

    // check for fork and step errors
    let error_count = if skip_static_step_fork_checks {
        0
    } else {
        static_fork_step_check::check_step_and_fork(&transactions_symbol_tables, diag)
    };
    if error_count > 0 {
        Err(anyhow!("step or fork errors"))
    } else {
        Ok(transactions_symbol_tables)
    }
}

pub type Traces = Vec<Vec<(String, Vec<baa::BitVecValue>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend<'a>(
    filename: impl AsRef<std::path::Path>,
    protos: impl Iterator<Item = &'a (ir::Transaction, ir::SymbolTable)>,
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    // Maps a transaction's name to its argument types
    let mut transaction_arg_types = rustc_hash::FxHashMap::default();
    for (tx, symbol_table) in protos {
        transaction_arg_types.insert(tx.name.clone(), tx.get_arg_types(symbol_table));
    }

    transactions_parser::parse_transactions_file(filename, diag, transaction_arg_types)
}
