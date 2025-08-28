// Copyright 2025 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::diagnostic::DiagnosticHandler;
use crate::errors::ExecutionError;
use crate::ir::{SymbolTable, Transaction};
use crate::parser::parsing_helper;
use crate::yosys::{ProjectConf, YosysEnv, yosys_to_btor};
use baa::BitVecValue;
use std::path::PathBuf;

/// Takes a path to a Verilog file and the name of a top-level module,
/// and returns a (Patronus `Context`, Patronus `TransitionSystem` pair)
fn create_sim_context(
    verilog_path: &str,
    top_module: Option<String>,
) -> (patronus::expr::Context, patronus::system::TransitionSystem) {
    let env = YosysEnv::default();
    let inp = PathBuf::from(verilog_path);
    let proj = ProjectConf::with_source(inp, top_module);

    let btor_file = yosys_to_btor(&env, &proj, None)
        .unwrap_or_else(|e| panic!("Failed to convert Verilog to BTOR: {}", e));

    // Check if btor file was actually created and has content
    if !btor_file.exists() {
        panic!("BTOR file was not created at path: {}", btor_file.display());
    }

    let metadata = std::fs::metadata(&btor_file)
        .unwrap_or_else(|e| panic!("Failed to read BTOR file metadata: {}", e));

    if metadata.len() == 0 {
        panic!("BTOR file is empty - likely synthesis failed. Check Yosys output for errors.");
    }

    patronus::btor2::parse_file(btor_file.as_path().as_os_str()).unwrap_or_else(|| {
        panic!(
            "Failed to parse BTOR file - possibly malformed: {}",
            btor_file.display()
        )
    })
}

/// Takes the following arguments and creates an environment for testing
/// - `verilog_path`: path to a Verilog file
/// - `transaction_filename`: path to a Protocol `.prot` file
/// - `top_module`: Name of the top-level module
/// - `handler`: a `DiagnosticHandler`
pub fn setup_test_environment(
    verilog_path: &str,
    transaction_filename: &str,
    top_module: Option<String>,
    handler: &mut DiagnosticHandler,
) -> (
    Vec<(Transaction, SymbolTable)>,    // owned
    patronus::expr::Context,            // owned
    patronus::system::TransitionSystem, // owned
) {
    let (ctx, sys) = create_sim_context(verilog_path, top_module);
    let parsed = parsing_helper(transaction_filename, handler);
    (parsed, ctx, sys)
}

/// Creates an owned bit-vector with a particular `value` & `width`
pub fn bv(value: u64, width: u32) -> BitVecValue {
    BitVecValue::from_u64(value, width)
}

/// Asserts that `res` is `Ok`
pub fn assert_ok(res: &Result<(), ExecutionError>) {
    assert!(res.is_ok(), "Expected Ok, got {:?}", res);
}

/// Asserts that `res` is `Err`
pub fn assert_err(res: &Result<(), ExecutionError>) {
    assert!(res.is_err(), "Expected Err, got {:?}", res);
}
