use crate::frontend::diagnostic::DiagnosticHandler;
use anyhow::anyhow;

pub mod ast;
pub mod diagnostic;
pub mod parser;
mod remap;
pub mod serialize;
pub mod static_checks;
pub mod static_fork_step_check;
pub mod symbol;
pub mod typecheck;

use crate::frontend::symbol::SymbolTable;
pub use remap::Module;

/// Simple frontend which loads protocol files, type checks and returns the Symbol Table and modules.
pub fn frontend(
    filenames: &[impl AsRef<std::path::Path>],
    diag: &mut DiagnosticHandler,
    skip_static_step_fork_checks: bool,
    allow_branch_on_arg: bool,
) -> anyhow::Result<(SymbolTable, Vec<Module>)> {
    // Parse protocols file
    let err = |e: String| {
        anyhow!(
            "{}: {}",
            e,
            filenames
                .iter()
                .map(|f| f.as_ref().to_string_lossy())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let mut ast = parser::parse_files(filenames, diag).map_err(err)?;

    // Type-check the parsed transactions
    typecheck::type_check(&mut ast, diag, allow_branch_on_arg)?;

    // check for fork and step errors
    let error_count = if skip_static_step_fork_checks {
        0
    } else {
        static_fork_step_check::check_step_and_fork(&ast, diag)
    };
    if error_count > 0 {
        anyhow::bail!("step or fork errors");
    }

    // implement remaps
    Ok(remap::to_modules(ast))
}

/// Picks a module if the module name is provided. Otherwise a single module is required.
pub fn pick_module(
    name: Option<&str>,
    modules: Vec<Module>,
    filenames: &[impl AsRef<std::path::Path>],
) -> anyhow::Result<Module> {
    if let Some(name) = name {
        let mod_names = module_names(&modules);
        if let Some(m) = modules.into_iter().find(|m| m.name == name) {
            Ok(m)
        } else {
            anyhow::bail!(
                "No module `{name}` found.\nThere are multiple structs/interfaces/modules in {}: {}.\nWe need to add a way to select which one we want to use.",
                file_names(filenames),
                mod_names,
            );
        }
    } else {
        require_single_module(modules, filenames)
    }
}

/// Succeeds iff there is only a single `struct` with protocols in the file.
pub fn require_single_module(
    mut modules: Vec<Module>,
    filenames: &[impl AsRef<std::path::Path>],
) -> anyhow::Result<Module> {
    if modules.is_empty() {
        anyhow::bail!(
            "No protocols found in {}",
            filenames
                .iter()
                .map(|f| f.as_ref().to_string_lossy())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if modules.len() > 1 {
        anyhow::bail!(
            "There are multiple structs/interfaces/modules in {}: {}.\nWe need to add a way to select which one we want to use.",
            file_names(filenames),
            module_names(&modules),
        );
    }
    Ok(modules.pop().unwrap())
}

fn module_names(modules: &[Module]) -> String {
    modules
        .iter()
        .map(|m| m.name.clone())
        .collect::<Vec<_>>()
        .join(", ")
}

fn file_names(filenames: &[impl AsRef<std::path::Path>]) -> String {
    filenames
        .iter()
        .map(|f| f.as_ref().to_string_lossy())
        .collect::<Vec<_>>()
        .join(", ")
}
