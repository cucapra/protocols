use crate::frontend::diagnostic::DiagnosticHandler;
use anyhow::anyhow;

pub mod ast;
pub mod design;
pub mod diagnostic;
pub mod errors;
pub mod parser;
pub mod serialize;
pub mod static_checks;
pub mod static_fork_step_check;
pub mod typecheck;

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
