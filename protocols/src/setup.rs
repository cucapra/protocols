// Copyright 2025-26 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::frontend;
use crate::frontend::ast::Protocol;
use crate::frontend::design::{Design, find_designs};
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::symbol::SymbolTable;

pub type TestEnv = (SymbolTable, Vec<Protocol>, Design);

/// Takes the following arguments and creates an environment for testing
/// - `verilog_paths`: paths to Verilog files
/// - `transaction_filename`: path to a Protocol `.prot` file
/// - `top_module`: Name of the top-level module
/// - `handler`: a `DiagnosticHandler`
pub fn setup_test_environment(
    transaction_filename: &str,
    handler: &mut DiagnosticHandler,
    skip_static_step_fork_checks: bool,
) -> anyhow::Result<TestEnv> {
    let (st, protos) = frontend(transaction_filename, handler, skip_static_step_fork_checks)?;
    let designs = find_designs(&st, &protos);
    assert!(!designs.is_empty(), "No protocol found!");
    assert_eq!(
        designs.len(),
        1,
        "TODO: deal with more than one struct defined in a single protocol"
    );
    let (_, design) = designs.into_iter().next().unwrap();
    Ok((st, protos, design))
}
