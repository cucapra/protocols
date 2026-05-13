// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use anyhow::anyhow;
use frontend::diagnostic::DiagnosticHandler;
use frontend::{ast, parser, static_fork_step_check, transactions_parser, typecheck};
use rustc_hash::FxHashMap;

pub mod backends;
pub mod frontend;
pub mod interpreter;
pub mod scheduler;
pub mod setup;
mod yosys;

use interpreter::Value;

/// Simple frontend which loads a single protocols file, type checks and returns the AST.
pub fn frontend(
    filename: impl AsRef<std::path::Path>,
    diag: &mut DiagnosticHandler,
    skip_static_step_fork_checks: bool,
) -> anyhow::Result<Vec<(ast::Protocol, ast::SymbolTable)>> {
    // Parse protocols file
    let mut transactions_symbol_tables: Vec<(ast::Protocol, ast::SymbolTable)> =
        parser::parse_file(filename, diag).map_err(|e| anyhow!(e))?;

    // Type-check the parsed transactions
    typecheck::type_check(&mut transactions_symbol_tables, diag)?;

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

pub type Traces = Vec<Vec<(String, Vec<Value>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend<'a>(
    filename: impl AsRef<std::path::Path>,
    protos: impl Iterator<Item = &'a (ast::Protocol, ast::SymbolTable)>,
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    let protos: FxHashMap<String, _> = protos.map(|(p, st)| (p.name.clone(), (p, st))).collect();
    transactions_parser::parse_transactions_file(filename, diag, &protos)
}
