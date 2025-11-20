// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use baa::BitVecValue;
use protocols::{
    ir::{StmtId, SymbolId, SymbolTable, Transaction},
    scheduler::NextStmtMap,
    serialize::serialize_stmt,
};
use rustc_hash::FxHashMap;

use crate::global_context::GlobalContext;

/// The local context associated with an individual thread,
/// storing information such as:
// - Which transaction are we currently running?
// - Where in the transaction are we currently at? (the `StmtId`)
// - A mutable map mapping variable names to their values (`args_mapping`)
#[derive(Debug, Clone)]
pub struct Thread {
    // The thread's ID
    pub thread_id: u32,

    /// The logical scheduling cycle in which the thread was started
    /// (This corresponds to the `logical_step` field in `WaveSignalTrace`,
    /// i.e. the no. of logical `step()` calls encountered in the program
    /// before this thread started)
    pub start_cycle: u32,

    /// The actual clock time-step in the waveform
    /// at which the thread began. (This corresponds to the `time_step`
    /// field in `WaveSignalTrace`.)
    pub start_time_step: u32,

    /// The `Transaction` that this `Thread` is running
    pub transaction: Transaction,

    /// The `SymbolTable` associated with the `Transaction`
    pub symbol_table: SymbolTable,

    /// The `NextStmtMap` associated with the `Transaction`
    pub next_stmt_map: NextStmtMap,

    /// Map storing the inferred values for the input and output arguments
    pub args_mapping: FxHashMap<SymbolId, BitVecValue>,

    /// Maps each `SymbolId` to a bit-string,
    /// where the `i`-th bit is 1 if it is known & 0 otherwise
    pub known_bits: FxHashMap<SymbolId, BitVecValue>,

    /// The current statement in the `Transaction`, identified by its `StmtId`
    pub current_stmt_id: StmtId,
}

/// Pretty-prints a `Thread`
impl std::fmt::Display for Thread {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "THREAD {}: {{ Start cycle: {}, Transaction: `{}`, Current stmt: `{}` ({}) }}",
            self.thread_id,
            self.start_cycle,
            self.transaction.name,
            serialize_stmt(&self.transaction, &self.symbol_table, &self.current_stmt_id),
            self.current_stmt_id
        )
    }
}

impl Thread {
    /// Creates a new `Thread` that given a `Transaction`, `SymbolTable`,
    /// `GlobalContext`, `thread_id` & `start_cycle`.
    /// This method also sets up the `args_mapping`
    /// accordingly based on the pins' values at the beginning of the signal trace.
    /// Note that `GlobalContext` is not a field in `Thread`, since we cannot
    /// derive `Clone` for `WaveSignalTrace`, but ideally we'd like to be able
    /// to clone `Thread`s.
    #[allow(unused_variables)]
    pub fn new(
        transaction: Transaction,
        symbol_table: SymbolTable,
        next_stmt_map: NextStmtMap,
        ctx: &GlobalContext,
        thread_id: u32,
        start_cycle: u32,
    ) -> Self {
        Self {
            thread_id,
            transaction: transaction.clone(),
            next_stmt_map,
            args_mapping: FxHashMap::default(),
            known_bits: FxHashMap::default(),
            symbol_table,
            current_stmt_id: transaction.body,
            start_cycle,
            start_time_step: ctx.trace.time_step(),
        }
    }
}
