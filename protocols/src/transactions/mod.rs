use rustc_hash::FxHashMap;

use crate::Value;
use crate::frontend::ast::Protocol;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::symbol::SymbolTable;

pub mod parser;

pub type Traces = Vec<Vec<(String, Vec<Value>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend<'a>(
    filename: impl AsRef<std::path::Path>,
    st: &'a SymbolTable,
    protos: &'a [Protocol],
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    let protos: FxHashMap<String, _> = protos.iter().map(|p| (p.name.clone(), p)).collect();
    parser::parse_transactions_file(filename, diag, st, &protos)
}
