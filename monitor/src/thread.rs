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

    /// The actual clock time-step in the waveform captured at the last step()
    /// statement before the thread completes. This represents when the transaction
    /// logically ends, before the final `step()` in the program (required
    /// by well-formedness constraints) advances the trace.
    /// This field is updated every time we encounter `step()` in the program
    /// and is initially set to `None`
    pub end_time_step: Option<u32>,

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

    /// Constraints on DUT input port values that must hold after stepping
    pub constraints: FxHashMap<SymbolId, BitVecValue>,

    /// The current statement in the `Transaction`, identified by its `StmtId`
    pub current_stmt_id: StmtId,

    /// Maps function parameters to DUT ports
    pub args_to_pins: FxHashMap<SymbolId, SymbolId>,
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
    /// `GlobalContext`, `thread_id` & `start_cycle` / `start_time_step`.
    /// This method also sets up the `args_mapping`
    /// accordingly based on the pins' values at the beginning of the signal trace.
    pub fn new(
        transaction: Transaction,
        symbol_table: SymbolTable,
        next_stmt_map: NextStmtMap,
        thread_id: u32,
        start_cycle: u32,
        start_time_step: u32,
    ) -> Self {
        Self {
            thread_id,
            transaction: transaction.clone(),
            next_stmt_map,
            args_mapping: FxHashMap::default(),
            known_bits: FxHashMap::default(),
            constraints: FxHashMap::default(),
            symbol_table,
            current_stmt_id: transaction.body,
            start_cycle,
            start_time_step,
            end_time_step: None, // Set when fork() is called
            args_to_pins: FxHashMap::default(),
        }
    }
}
