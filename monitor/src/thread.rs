// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::collections::HashMap;

use protocols::{
    ir::{StmtId, SymbolTable, Transaction},
    scheduler::NextStmtMap,
};

use crate::{
    global_context::GlobalContext,
    signal_trace::{PortKey, SignalTrace},
};

/// The local context associated with an individual thread,
/// storing information such as:
// - Which transaction are we currently running?
// - Where in the transaction are we currently at? (the `StmtId`)
// - A mutable map mapping variable names to their values (`args_mapping`)
#[derive(Debug, Clone)]
pub struct Thread {
    // The thread's ID
    pub thread_id: u32,

    /// The cycle in which the thread was started
    pub start_cycle: u32,

    /// The `Transaction` that this `Thread` is running
    pub transaction: Transaction,

    /// The `SymbolTable` associated with the `Transaction`
    pub symbol_table: SymbolTable,

    /// The `NextStmtMap` associated with the `Transaction`
    pub next_stmt_map: NextStmtMap,

    /// The current statement in the `Transaction`, identified by its `StmtId`
    pub current_stmt_id: StmtId,
}

impl Thread {
    /// Creates a new `Thread` that given a `Transaction`, `SymbolTable`,
    /// `GlobalContext`, `thread_id` & `start_cycle`.
    /// This method also sets up the `args_mapping`
    /// accordingly based on the pins' values at the beginning of the signal trace.
    /// Note that `GlobalContext` is not a field in `Thread`, since we cannot
    /// derive `Clone` for `WaveSignalTrace`, but ideally we'd like to be able
    /// to clone `Thread`s.
    pub fn new(
        transaction: Transaction,
        symbol_table: SymbolTable,
        next_stmt_map: NextStmtMap,
        ctx: &GlobalContext,
        thread_id: u32,
        start_cycle: u32,
    ) -> Self {
        let mut args_mapping = HashMap::new();

        for port_key in ctx.trace.port_map.keys() {
            // We assume that there is only one `Instance` at the moment
            let PortKey {
                instance_id,
                pin_id,
            } = port_key;

            // Fetch the current value of the `pin_id`
            // (along with the name of the corresponding `Field`)
            let current_value = ctx.trace.get(*instance_id, *pin_id).unwrap_or_else(|err| {
                panic!(
                    "Unable to get value for pin {pin_id} in signal trace, {:?}",
                    err
                )
            });
            args_mapping.insert(*pin_id, current_value);
        }

        Self {
            thread_id,
            transaction: transaction.clone(),
            next_stmt_map,
            symbol_table,
            current_stmt_id: transaction.body,
            start_cycle,
        }
    }
}
