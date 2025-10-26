// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::collections::HashMap;

use baa::BitVecValue;
use log::info;
use protocols::{
    ir::{StmtId, SymbolId, SymbolTable, Transaction},
    scheduler::NextStmtMap,
    serialize::{serialize_bitvec, serialize_stmt},
};

use crate::{global_context::GlobalContext, signal_trace::SignalTrace};

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

    /// Map storing the inferred values for the input and output arguments
    pub args_mapping: HashMap<SymbolId, BitVecValue>,

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
        args_mapping: HashMap<SymbolId, BitVecValue>,
        ctx: &GlobalContext,
        thread_id: u32,
        start_cycle: u32,
    ) -> Self {
        let mut args_mapping = HashMap::new();
        info!("Creating new thread");

        // Map input parameters to their corresponding DUT pin values
        // e.g. 'a' |-> value of 'DUT.a' from the trace at current cycle

        // Obtain the name of the DUT
        let dut_name = symbol_table[ctx.design.symbol_id].name();
        for arg in &transaction.args {
            let param_symbol_id = arg.symbol();
            let param_name = symbol_table[param_symbol_id].name();

            // Find the corresponding DUT pin (e.g., "DUT.a" for parameter "a")
            let dut_pin_name = format!("{}.{}", dut_name, param_name);
            let dut_pin_symbol_id = symbol_table
                .symbol_id_from_name(&dut_pin_name)
                .unwrap_or_else(|| {
                    panic!(
                        "Unable to find DUT pin '{}' for transaction parameter '{}'",
                        dut_pin_name, param_name
                    )
                });

            // Fetch the current value of the DUT pin from the trace
            let current_value = ctx
                .trace
                .get(ctx.instance_id, dut_pin_symbol_id)
                .unwrap_or_else(|err| {
                    panic!(
                        "Unable to get value for DUT pin {} in signal trace, {:?}",
                        dut_pin_name, err
                    )
                });

            info!(
                "Inserting ({}, {}) into args_mapping...",
                symbol_table.full_name_from_symbol_id(&param_symbol_id),
                serialize_bitvec(&current_value, ctx.display_hex)
            );

            // Map the transaction parameter to the DUT pin's value
            args_mapping.insert(param_symbol_id, current_value);
        }

        Self {
            thread_id,
            transaction: transaction.clone(),
            next_stmt_map,
            args_mapping,
            symbol_table,
            current_stmt_id: transaction.body,
            start_cycle,
        }
    }
}
