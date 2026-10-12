use crate::Value;
use crate::frontend::ast::Protocol;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::symbol::SymbolTable;

pub mod parser;

pub type Traces = Vec<Vec<(String, Vec<Value>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend(
    filename: impl AsRef<std::path::Path>,
    st: &SymbolTable,
    protos: &[Protocol],
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    parser::parse_transactions_file(filename, diag, st, protos)
}
