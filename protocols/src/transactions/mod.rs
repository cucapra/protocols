use rustc_hash::FxHashMap;

use crate::Value;
use crate::frontend::ast::Ast;
use crate::frontend::diagnostic::DiagnosticHandler;

pub mod parser;

pub type Traces = Vec<Vec<(String, Vec<Value>)>>;

/// Simple frontend for loading a transaction trace file (*.tx)
pub fn transaction_frontend(
    filename: impl AsRef<std::path::Path>,
    ast: &Ast,
    diag: &mut DiagnosticHandler,
) -> anyhow::Result<Traces> {
    let protos: FxHashMap<String, _> = ast.protos.iter().map(|p| (p.name.clone(), p)).collect();
    parser::parse_transactions_file(filename, diag, &ast.st, &protos)
}
