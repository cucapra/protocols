use crate::frontend::ast;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::interpreter::Value;
use rustc_hash::FxHashMap;

pub mod parser;

pub type Traces = Vec<Vec<(String, Vec<Value>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend<'a>(
    filename: impl AsRef<std::path::Path>,
    protos: impl Iterator<Item = &'a (ast::Protocol, ast::SymbolTable)>,
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    let protos: FxHashMap<String, _> = protos.map(|(p, st)| (p.name.clone(), (p, st))).collect();
    parser::parse_transactions_file(filename, diag, &protos)
}
