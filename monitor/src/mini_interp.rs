use std::collections::HashMap;

use baa::BitVecValue;
use protocols::ir::{StmtId, SymbolId, SymbolTable, Transaction};
use rustc_hash::FxHashMap;

/// A "mini" interpreter for Protocols programs, to be used in conjunction
/// with the monitor.
/// - This is "mini" in the sense that it does not rely on Patronus/Yosys,
///   and it only supports a subset of the Protocols language so far.
#[allow(dead_code)]
#[derive(Debug)]
pub struct MiniInterpreter<'a> {
    tr: &'a Transaction,
    st: &'a SymbolTable,
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,
    // `HashMap` mapping `SymbolId`s to their values
    args_mapping: HashMap<SymbolId, BitVecValue>,
}

#[allow(dead_code)]
impl<'a> MiniInterpreter<'a> {
    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.tr.format_stmt(stmt_id, self.st)
    }

    /// Creates a new `MiniInterpreter` given a `Transaction` and a `SymbolTable`
    pub fn new(tr: &'a Transaction, st: &'a SymbolTable) -> Self {
        Self {
            tr,
            st,
            next_stmt_map: tr.next_stmt_mapping(),
            args_mapping: HashMap::new(),
        }
    }

    // Update the `args_mapping` with the `current_value` for the `pin_id`
    pub fn update_arg_value(&mut self, pin_id: SymbolId, value: BitVecValue) {
        self.args_mapping.insert(pin_id, value);
    }
}
