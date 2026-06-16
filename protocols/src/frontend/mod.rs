use anyhow::anyhow;

use crate::frontend::diagnostic::DiagnosticHandler;

pub mod ast;
pub mod design;
pub mod diagnostic;
pub mod parser;
pub mod serialize;
pub mod static_checks;
pub mod static_fork_step_check;
pub mod symbol;
pub mod typecheck;

/// Simple frontend which loads a single protocols file, type checks and returns the AST.
pub fn frontend(
    filenames: &[impl AsRef<std::path::Path>],
    diag: &mut DiagnosticHandler,
    skip_static_step_fork_checks: bool,
) -> anyhow::Result<(symbol::SymbolTable, Vec<ast::Protocol>)> {
    // Parse protocols file
    let (mut st, protos, remaps) = parser::parse_files(filenames, diag).map_err(|e| {
        anyhow!(
            "{}: {}",
            e,
            filenames
                .iter()
                .map(|f| f.as_ref().to_string_lossy())
                .collect::<Vec<_>>()
                .join(", ")
        )
    })?;

    // Type-check the parsed transactions
    typecheck::type_check(&mut st, &protos, &remaps, diag)?;

    // check for fork and step errors
    let error_count = if skip_static_step_fork_checks {
        0
    } else {
        static_fork_step_check::check_step_and_fork(&st, &protos, diag)
    };
    if error_count > 0 {
        Err(anyhow!("step or fork errors"))
    } else {
        Ok((st, protos))
    }
}
