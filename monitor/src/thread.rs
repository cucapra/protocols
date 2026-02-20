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

use crate::{global_context::GlobalContext, types::LoopArgState};

/// The local context associated with an individual thread,
/// storing information such as:
// - Which transaction are we currently running?
// - Where in the transaction are we currently at? (the `StmtId`)
// - A mutable map mapping variable names to their values (`args_mapping`)
#[derive(Debug, Clone)]
pub struct Thread {
    /// Name of the scheduler/struct this thread belongs to
    /// (Used to create globally unique thread identifiers in multi-struct mode)
    pub scheduler_name: String,

    // The thread's ID (unique within this scheduler)
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

    /// Constraints on DUT input port values that must hold after stepping
    pub constraints: FxHashMap<SymbolId, BitVecValue>,

    /// The current statement in the `Transaction`, identified by its `StmtId`
    pub current_stmt_id: StmtId,

    /// Maps function parameters to DUT ports
    pub args_to_pins: FxHashMap<SymbolId, SymbolId>,

    /// Maps arguments of `repeat` loops to their current "guessed" state
    /// (either `Speculative` or `Known` -- see docs for the `LoopArgState` type)
    pub loop_args_state: FxHashMap<SymbolId, LoopArgState>,

    /// Once the state of a `LoopArg` has been determined, we need to track
    /// how many iterations remain to be executed -- this is most useful
    /// if we have two loops that use the same `LoopArg`, e.g.
    /// `repeat n iterations { ... }; ...; repeat n iterations { ...}`.
    /// This map is populated lazily when we encounter each `repeat` loop
    /// (see `Scheduler::run_thread_till_next_step`).
    /// The `StmtId` key is the statement of the `repeat` loop.
    pub repeat_loops_remaining_iters: FxHashMap<StmtId, u64>,

    /// Determines if the thread has called `fork()` yet. Initialized to `false`.
    /// Since well-formedness dicates that a protocol can only contain
    /// at most one `fork()`, once this flag is set to `true`,
    /// it remains `true` for the rest of the thread's execution.
    pub has_forked: bool,
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
    /// Creates a new `Thread` given the following:
    /// - a `scheduler_name` (the name of the corresponding struct)
    /// - a `Transaction`
    /// - a `SymbolTable`
    /// - a `GlobalContext`
    /// - a `thread_id`
    /// - a `start_cycle` / `start_time_step`
    ///   This method also sets up the `args_mapping`
    ///   accordingly based on the pins' values at the beginning of the signal trace.
    pub fn new(
        scheduler_name: String,
        transaction: Transaction,
        symbol_table: SymbolTable,
        next_stmt_map: NextStmtMap,
        thread_id: u32,
        start_cycle: u32,
        start_time_step: u32,
    ) -> Self {
        Self {
            scheduler_name,
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
            args_to_pins: FxHashMap::default(),
            has_forked: false,
            loop_args_state: FxHashMap::default(),
            repeat_loops_remaining_iters: FxHashMap::default(),
        }
    }

    /// Returns an ID for the thread that is unique across all schedulers.
    /// If there are multiple structs, this function prefixes the thread ID with
    /// the struct name (same as the scheduler name). Otherwise,
    /// this functio just returns the regular thread ID.
    pub fn global_thread_id(&self, ctx: &GlobalContext) -> String {
        if ctx.multiple_structs {
            format!("{}::{}", self.scheduler_name, self.thread_id)
        } else {
            format!("{}", self.thread_id)
        }
    }
}
