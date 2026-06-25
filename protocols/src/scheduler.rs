// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Value;
use crate::dut::PatronusSim;
use crate::errors::{DiagnosticEmitter, ExecutionError, ExecutionResult};
use crate::frontend::ast::*;
use crate::frontend::diagnostic::DiagnosticHandler;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::interpreter::{Evaluator, ThreadInputValue};
use baa::{BitVecOps, BitVecValue};
use log::info;
use rustc_hash::FxHashMap;

/// `NextStmtMap` allows us to interpret without using recursion
/// (the interpreter can just look up what the next statement is using this map)
pub type NextStmtMap = FxHashMap<StmtId, Option<StmtId>>;
type ArgMap<'a> = FxHashMap<&'a str, Value>;

/// An `Invocation` is a pair consisting of the `String` of the `Protocol` to instantiate and a `Vec<Value>` of arguments to the protocol
pub type Invocation = (String, Vec<Value>);

/// A `ProtocolInfo` is a triple of the form
/// `(Protocol, SymbolTable, NextStmtMap)`.
/// This is passed to the interpreter when we want to execute
/// a single protocol.
type ProtocolInfo<'a> = (&'a Protocol, &'a SymbolTable, NextStmtMap);

/// A `Transaction` is a protocol instantiation
#[derive(Debug, Clone)]
pub struct Transaction<'a> {
    pub proto: &'a Protocol,
    pub st: &'a SymbolTable,
    /// The associated argument values (a map from variable names to their values)
    pub args: ArgMap<'a>,
    pub next_stmt_map: NextStmtMap,
}

impl<'a> Transaction<'a> {
    pub fn new(
        tr: &'a Protocol,
        st: &'a SymbolTable,
        args: ArgMap<'a>,
        next_stmt_map: NextStmtMap,
    ) -> Self {
        Self {
            proto: tr,
            st,
            args,
            next_stmt_map,
        }
    }

    /// Pretty-prints a `Statement` based on its `StmtId`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.proto.format_stmt(stmt_id, self.st)
    }
}

/// Struct containing metadata associated with a `Thread`
#[derive(Debug, Clone)]
pub struct Thread<'a> {
    /// The corresponding `Transaction`
    pub transaction: Transaction<'a>,
    /// The `StmtId` of the current step
    pub current_step: StmtId,
    /// The `StmtId` of the next step (if one exists)
    pub next_step: Option<StmtId>,
    /// Whether the thread has `has_stepped` already
    pub has_stepped: bool,
    /// Whether the thread `has_forked` already
    pub has_forked: bool,
    /// The `StmtId` of the previous fork (if one exists)
    /// (This is used to allow more precise error messages for `DoubleFork` errors)
    pub prev_fork_stmt_id: Option<StmtId>,
    /// Index into the original `invocs` and parallel `results` vector (used to store this thread's result)
    pub tx_idx: usize,
    /// copy of the loop_vars in the Evaluator for context switching
    pub loop_vars: Vec<(SymbolId, BitVecValue)>,
    /// copy of the loop_info in the Evaluator for context switching
    pub loop_info: Vec<(StmtId, u64, u64)>,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(tx: Transaction<'a>, tx_idx: usize) -> Self {
        info!(
            "Thread initialized with transaction: {:?}, thread_id={}",
            tx.proto.name, tx_idx
        );
        Self {
            current_step: tx.proto.body,
            next_step: None,
            tx_idx,
            loop_vars: vec![],
            transaction: tx,
            prev_fork_stmt_id: None,
            has_stepped: false,
            has_forked: false,
            loop_info: vec![],
        }
    }

    /// Pretty-prints a `Statement` identified by its `StmtId`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.transaction.format_stmt(stmt_id)
    }

    /// Sets the next step and writes back bounded loop state from the evaluator.
    /// Called when thread execution pauses (at step, on error, or on completion).
    pub fn save_state(
        &mut self,
        next_step: Option<StmtId>,
        loop_vars: Vec<(SymbolId, BitVecValue)>,
        loop_info: Vec<(StmtId, u64, u64)>,
    ) {
        self.next_step = next_step;
        self.loop_vars = loop_vars;
        self.loop_info = loop_info;
    }
}

pub enum StepResult<'a> {
    /// Thread hit a Step and should be re-scheduled
    Continue(Thread<'a>),
    /// Thread ran to completion (no more statements)
    Completed(usize /* thread_id */),
    /// Thread errored out
    Error(usize /* thread_id */, ExecutionError),
}

/// The `Scheduler` struct contains metadata necessary for scheduling `Thread`s.
pub struct Scheduler<'a> {
    sim: PatronusSim,
    proto_infos: Vec<ProtocolInfo<'a>>,
    /// A list of `Invocation`s to be executed (each element corresponds to a function call in a `.tx` file)
    invocs: Vec<Invocation>,
    /// The index of the next element in `invocs` to be executed when we `fork`
    next_tx_idx: usize,
    /// A list of currently active threads
    active_threads: Vec<Thread<'a>>,
    /// The scheduler's ready queue, storing all threads to be executed next
    next_threads: Vec<Thread<'a>>,
    /// A list of inactive threads (threads that have finished execution)
    inactive_threads: Vec<Thread<'a>>,
    /// The current scheduling cycle
    step_count: u32,
    /// The max no. of steps allowed in the interpreter
    max_steps: u32,
    /// The associated `Evaluator` (interpreter) for evaluating Protocols programs
    evaluator: Evaluator<'a>,
    /// A `Vec` storing the `ExecutionResult`s of each thread
    results: Vec<ExecutionResult<()>>,
    /// Handler for error diagnostics
    handler: &'a mut DiagnosticHandler,
    /// Flag that tracks whether any thread executed a `step()` statement
    /// in the current scheduling cycle. This is used to ensure
    /// that the simulator's `sim_step()` method is called even when all
    /// threads have completed and the `next_threads` queue is empty
    /// (this is necessary to produce accurate waveforms for combinational
    /// DUTs that only have one single `step()` in their protocol).
    step_happened_this_cycle: bool,
}

impl<'a> Scheduler<'a> {
    // Helper method that creates a `Transaction` struct
    fn next_transaction_helper(
        invocs: &[Invocation],
        idx: usize,
        proto_infos: &[ProtocolInfo<'a>],
    ) -> Option<Transaction<'a>> {
        if idx < invocs.len() {
            // get the corresponding transaction, symbol table, and next_stmt_map
            let tr_name = invocs[idx].0.clone();

            // find the ir corresponding to the transaction name
            let proto_idx = proto_infos
                .iter()
                .position(|(tr, _, _)| tr.name == tr_name)
                .expect("Transaction not found amongst declared protocols.");
            let (tr, st, next_stmt_map) = &proto_infos[proto_idx];

            // set up the arguments for the transaction
            let args = invocs[idx].1.clone();
            let mut args_map = FxHashMap::default();

            for (i, arg) in args.iter().enumerate() {
                let identifier = st[tr.args[i].symbol()].name();
                args_map.insert(identifier, arg.clone());
            }

            Some(Transaction::new(tr, st, args_map, next_stmt_map.clone()))
        } else {
            None
        }
    }

    fn next_transaction(&self, idx: usize) -> Option<Transaction<'a>> {
        Self::next_transaction_helper(&self.invocs, idx, &self.proto_infos)
    }

    pub fn new(
        st: &'a SymbolTable,
        protos: &'a [Protocol],
        invocs: Vec<Invocation>,
        sim: PatronusSim,
        handler: &'a mut DiagnosticHandler,
        max_steps: u32,
    ) -> Self {
        // Create `ProtocolInfo`s with pre-computed next statement mappings
        let proto_infos: Vec<ProtocolInfo<'a>> = protos
            .iter()
            .map(|proto| (proto, st, proto.next_stmt_mapping()))
            .collect();

        // set up the Evaluator and first Thread
        let initial_tx = Self::next_transaction_helper(&invocs, 0, &proto_infos)
            .expect("No transactions passed.");

        info!(
            "Starting with initial transaction: {:?}",
            initial_tx.proto.name
        );

        // Initialize evaluator with first transaction
        let evaluator = Evaluator::new(
            initial_tx.args.clone(),
            initial_tx.proto,
            initial_tx.st,
            &sim,
        );

        let results_size = invocs.len();
        let first = Thread::initialize_thread(initial_tx, 0);

        info!("Added first thread to active_threads");
        Self {
            proto_infos,
            invocs,
            next_tx_idx: 1,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 0,
            evaluator,
            results: vec![Ok(()); results_size],
            handler,
            max_steps,
            step_happened_this_cycle: false,
            sim,
        }
    }

    /// Runs the scheduler on a list of transaction, returning a list of `ExecutionResult`s
    pub fn execute_transactions(&mut self) -> Vec<ExecutionResult<()>> {
        info!(
            "==== Starting scheduling cycle {}, active threads: {} ====",
            self.step_count + 1,
            self.active_threads.len()
        );

        while !self.active_threads.is_empty() {
            // Run all threads with assertions and forks enabled
            // Keep running newly forked threads in the same cycle
            self.evaluator.enable_assertions();
            let mut start_idx = 0;
            loop {
                let end_idx = self.active_threads.len();

                // Run threads from start_idx to end_idx (only new threads)
                for i in start_idx..end_idx {
                    self.run_thread_until_next_step(i, true);
                }

                // Move newly forked threads from next_threads to active_threads
                // so they run in the same cycle (important for detecting conflicts)
                if !self.next_threads.is_empty() {
                    info!(
                        "Moving {} threads from next_threads to active_threads",
                        self.next_threads.len()
                    );
                    start_idx = self.active_threads.len(); // Next iteration starts from here
                    self.active_threads.append(&mut self.next_threads);
                } else {
                    // No new threads forked, we're done with this cycle
                    break;
                }
            }

            // Check for conflicting assignments after all threads have run
            let conflict_errors = self.check_for_conflicts();
            if !conflict_errors.is_empty() {
                info!("Conflicting assignment detected, terminating all threads");
                // Mark each conflicting thread with its own error (using its own stmt_id)
                for (thread_idx, error) in conflict_errors {
                    self.results[thread_idx] = Err(error);
                }
                // Clear all threads to stop execution
                self.active_threads.clear();
                self.next_threads.clear();
                break;
            }

            // No conflicts - finalize input values to sim before stepping
            self.evaluator.finalize_inputs_for_cycle(&mut self.sim);

            // Collect threads that need implicit forking (can't call self.next_transaction during drain)
            let mut threads_needing_implicit_fork: Vec<usize> = Vec::new();

            // Move each active thread into inactive or next (drain preserves order)
            for mut active_thread in self.active_threads.drain(..) {
                let next_step: Option<StmtId> = active_thread.next_step;
                match next_step {
                    Some(next_step_id) => {
                        info!(
                            "Thread with transaction {:?} reached `Step()`, moving to next_threads with `Step()`: {:?}",
                            active_thread.transaction.proto.name, next_step_id
                        );

                        // if the thread is moving to next_threads, its current_step becomes its next_step and next_step becomes None
                        active_thread.current_step = next_step_id;
                        active_thread.next_step = None;
                        self.next_threads.push(active_thread)
                    }
                    None => {
                        info!(
                            "Thread with transaction {:?} finished execution, moving to inactive_threads",
                            active_thread.transaction.proto.name
                        );
                        // Clear thread inputs
                        self.evaluator.clear_thread_inputs(active_thread.tx_idx);

                        // Track if this thread needs implicit fork
                        if !active_thread.has_forked && self.results[active_thread.tx_idx].is_ok() {
                            threads_needing_implicit_fork.push(active_thread.tx_idx);
                        }

                        self.inactive_threads.push(active_thread)
                    }
                }
            }

            if threads_needing_implicit_fork.len() > 1 {
                info!("TODO: there should only be a single thread forking at one time.");
            }

            // Process implicit forks after drain is complete
            for _tx_idx in threads_needing_implicit_fork {
                let next_transaction_option = self.next_transaction(self.next_tx_idx);
                match next_transaction_option {
                    Some(tx) => {
                        let new_thread = Thread::initialize_thread(tx, self.next_tx_idx);
                        self.next_threads.push(new_thread);
                        info!(
                            "    enqueued implicitly forked thread; queue size = {}",
                            self.next_threads.len()
                        );
                    }
                    None => {
                        info!("    no more transactions to fork, skipping implicit fork.");
                    }
                }
                self.next_tx_idx += 1;
            }

            // Advance the simulator whenever a `step()` statement was
            // encountered this cycle.
            // This must happen even when all threads have completed and
            // the `next_threads` queue is empty, so that the waveform
            // records a timestep for every `step()` statement in the protocol.
            // (Example: combinational adders which only contain one `step()`.
            // Without the following if-statement, the waveform would contain
            // 0 timesteps.)
            if self.step_happened_this_cycle {
                info!("Stepping...");
                self.sim.step();
                // Reset flag to ensure that simulator is stepped exactly
                // once during each cycle
                self.step_happened_this_cycle = false;
            }

            // set up the threads for the next cycle
            if !self.next_threads.is_empty() {
                info!(
                    "Moving {} threads from next_threads to active_threads for next cycle",
                    self.next_threads.len()
                );
                self.active_threads = std::mem::take(&mut self.next_threads);
                self.step_count += 1;
                info!("Advancing to scheduling cycle: {}", self.step_count + 1);
                if self.step_count >= self.max_steps {
                    // Emit error for all active threads
                    for thread in &self.active_threads {
                        self.results[thread.tx_idx] =
                            Err(ExecutionError::MaxStepsReached(self.max_steps));
                    }
                    // shut down execution by clearing all active threads
                    self.active_threads.clear();
                }
            } else {
                info!("No more threads to schedule. Execution complete.");
            }
        }

        // Emit diagnostics for all errors after execution is complete
        self.emit_all_diagnostics();
        self.results.clone()
    }

    /// Checks for conflicting assignments across all threads at end of cycle.
    /// Returns a list of (thread_idx, error) for each thread involved in a conflict.
    fn check_for_conflicts(&self) -> Vec<(usize, ExecutionError)> {
        let mut errors = Vec::new();
        let per_thread_input_vals = self.evaluator.per_thread_input_vals();

        for (port_id, per_thread_vals) in per_thread_input_vals {
            // Collect all concrete values with their thread indices and stmt_ids
            let concrete_vals: Vec<(usize, &BitVecValue, Option<StmtId>)> = per_thread_vals
                .iter()
                .filter_map(|(&tx_idx, (val, stmt_id))| {
                    if let ThreadInputValue::Concrete(bvv) = val {
                        Some((tx_idx, bvv, *stmt_id))
                    } else {
                        None
                    }
                })
                .collect();

            // Check if any two concrete values differ
            if concrete_vals.len() >= 2 {
                let (first_idx, first_val, first_stmt_id) = &concrete_vals[0];
                for (second_idx, second_val, second_stmt_id) in &concrete_vals[1..] {
                    if !first_val.is_equal(*second_val) {
                        let first_transaction_name = self.invocs[*first_idx].0.clone();
                        let second_transaction_name = self.invocs[*second_idx].0.clone();
                        let port_name = self.sim.port_name(*port_id);

                        // Error for first thread
                        errors.push((
                            *first_idx,
                            ExecutionError::conflicting_assignment(
                                port_name.into(),
                                (*second_val).clone(),
                                (*first_val).clone(),
                                *first_idx,
                                first_transaction_name,
                                first_stmt_id.expect("Concrete values should have stmt_id"),
                            ),
                        ));

                        // Error for second thread
                        errors.push((
                            *second_idx,
                            ExecutionError::conflicting_assignment(
                                port_name.into(),
                                (*first_val).clone(),
                                (*second_val).clone(),
                                *second_idx,
                                second_transaction_name,
                                second_stmt_id.expect("Concrete values should have stmt_id"),
                            ),
                        ));

                        return errors;
                    }
                }
            }
        }
        errors
    }

    fn emit_all_diagnostics(&mut self) {
        // results and txs are parallel arrays, so we can use the same idx
        for (idx, result) in self.results.iter().enumerate() {
            if let Err(error) = result {
                let ir_idx = self
                    .proto_infos
                    .iter()
                    .position(|(tr, _, _)| tr.name == self.invocs[idx].0.clone())
                    .expect("Transaction not found in declared protocols.");
                let (tr, st, _) = self.proto_infos[ir_idx];

                DiagnosticEmitter::emit_execution_error(
                    self.handler,
                    error,
                    tr,
                    st,
                    &self.invocs[idx].1,
                );
            }
        }
    }

    /// Runs every active thread up to the next step to synchronize on
    pub fn run_all_active_until_next_step(&mut self, forks_enabled: bool) {
        for i in 0..self.active_threads.len() {
            self.run_thread_until_next_step(i, forks_enabled);
        }
    }

    /// Runs a single thread (indicated by its `thread_idx`) until the next step to synchronize on
    pub fn run_thread_until_next_step(&mut self, thread_idx: usize, forks_enabled: bool) {
        let next_transaction_option = self.next_transaction(self.next_tx_idx);
        let thread = &mut self.active_threads[thread_idx];
        let mut current_stmt_id = thread.current_step;

        info!(
            "Running thread {} from `step()` ({})",
            thread.transaction.proto.name, current_stmt_id
        );

        info!("  BEFORE context_switch");
        self.evaluator.context_switch(thread.clone());
        info!("  AFTER context_switch");

        // Initialize thread inputs at cycle START (implicit reapplication)
        info!(
            "  About to call init_thread_inputs for tx_idx={} ({})",
            thread.tx_idx, thread.transaction.proto.name
        );
        if let Err(e) = self
            .evaluator
            .init_thread_inputs(&mut self.sim, thread.tx_idx)
        {
            info!(
                "ERROR during init_thread_inputs: {:?}, terminating thread",
                e
            );
            self.results[thread.tx_idx] = Err(e);
            thread.save_state(
                None,
                self.evaluator.loop_vars.clone(),
                self.evaluator.loop_info.clone(),
            );
            return;
        }

        // tracks if we have encountered an assign or assert statement
        // we only fire the last statement is not a step if this is true
        let mut has_done_useful_work = false;

        // keep evaluating until we hit a Step, hit the end, or error out:
        loop {
            info!(
                "  Evaluating statement: `{}`",
                thread.format_stmt(&current_stmt_id)
            );

            match self.evaluator.evaluate_stmt(&mut self.sim, current_stmt_id) {
                // happy path: got a next statement
                Ok(Some(next_id)) => {
                    info!(
                        "  Next statement: {:?} `{}`",
                        next_id,
                        thread.format_stmt(&next_id)
                    );

                    match thread.transaction.proto[next_id] {
                        Stmt::Step => {
                            // We've encountered a step, so set `has_stepped` to true
                            if !thread.has_stepped {
                                thread.has_stepped = true;
                            }
                            self.step_happened_this_cycle = true;
                            info!("  `Step()` reached at {:?}, pausing.", next_id);

                            // Check if this is the final step (no statement after it)
                            // If so, thread completes at this cycle rather than running another useless cycle
                            let next_step =
                                if thread.transaction.next_stmt_map.get(&next_id) == Some(&None) {
                                    info!("  This is the final step, thread completes.");
                                    None
                                } else {
                                    Some(next_id)
                                };
                            thread.save_state(
                                next_step,
                                self.evaluator.loop_vars.clone(),
                                self.evaluator.loop_info.clone(),
                            );
                            return;
                        }

                        Stmt::Fork if forks_enabled => {
                            if thread.has_forked {
                                info!(
                                    "  ERROR: Thread has already forked at this point, terminating thread"
                                );
                                let error = ExecutionError::double_fork(
                                    thread.tx_idx,
                                    thread.transaction.proto.name.clone(),
                                    thread.prev_fork_stmt_id.expect("Forked multiple times but `prev_fork_stmt_id` field is `None`"),
                                    next_id,
                                );
                                self.results[thread.tx_idx] = Err(error);
                                thread.save_state(
                                    None,
                                    self.evaluator.loop_vars.clone(),
                                    self.evaluator.loop_info.clone(),
                                );
                                return;
                            } else if !thread.has_stepped {
                                info!(
                                    "  ERROR: fork() called before step() in this thread, terminating thread"
                                );
                                thread.has_forked = true;
                                let error = ExecutionError::fork_before_step(
                                    thread.tx_idx,
                                    thread.transaction.proto.name.clone(),
                                    next_id,
                                );
                                self.results[thread.tx_idx] = Err(error);
                                thread.save_state(
                                    None,
                                    self.evaluator.loop_vars.clone(),
                                    self.evaluator.loop_info.clone(),
                                );
                                return;
                            }

                            info!("  `Fork` at stmt_id {}, spawning new thread…", next_id);
                            match next_transaction_option.clone() {
                                Some(tx) => {
                                    let new_thread =
                                        Thread::initialize_thread(tx, self.next_tx_idx);

                                    self.next_threads.push(new_thread);
                                    info!(
                                        "    enqueued forked thread; queue size = {}",
                                        self.next_threads.len()
                                    );
                                }
                                None => {
                                    info!("    no more transactions to fork, skipping fork.");
                                }
                            }
                            self.next_tx_idx += 1;
                            // Mark this thread as having forked
                            info!(
                                "  Marking thread {} (tx_idx {}) as having forked.",
                                thread.transaction.proto.name, thread.tx_idx
                            );
                            // continue from the fork point
                            current_stmt_id = next_id;
                            // Update fields in the `Thread` struct that track whether
                            // we've forked already
                            thread.has_forked = true;
                            thread.prev_fork_stmt_id = Some(next_id);
                        }
                        Stmt::AssertEq(_, _) | Stmt::Assign(_, _) => {
                            has_done_useful_work = true;
                            current_stmt_id = next_id;
                        }
                        _ => {
                            // default "just keep going" case
                            current_stmt_id = next_id;
                        }
                    }
                }

                // no more statements -> done
                Ok(None) => {
                    let thread_id = thread.tx_idx;
                    let transaction_name = thread.transaction.proto.name.clone();

                    // Check if the last executed statement was `step()`
                    if let Stmt::Step = thread.transaction.proto[current_stmt_id] {
                        // Thread completed execution successfully
                        // If the thread hasn't forked yet, implicit fork will happen below
                        info!("  Execution complete, no more statements.");
                    } else if has_done_useful_work {
                        // Last executed statement wasn't `step()`, report an error
                        info!(
                            " ERROR: Last executed statement in this thread wasn't `step()`, terminating thread"
                        );
                        let error = ExecutionError::didnt_end_with_step(
                            thread_id,
                            transaction_name,
                            current_stmt_id,
                        );
                        self.results[thread_id] = Err(error);
                    }
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    info!("ERROR: {:?}, terminating thread", e);
                    self.results[thread.tx_idx] = Err(e);
                    break;
                }
            }
        }
        // Save thread state after execution pauses (loop exited via break)
        thread.save_state(
            None,
            self.evaluator.loop_vars.clone(),
            self.evaluator.loop_info.clone(),
        );

        // Clear this thread's inputs if it completed (before implicit fork so new thread starts fresh)
        if thread.next_step.is_none() {
            self.evaluator.clear_thread_inputs(thread.tx_idx);
        }

        // fork if a thread has completed successfully
        // more specifically, if forks are enabled, and this thread has None for next_step, and the thread didn't fail
        if !thread.has_forked && forks_enabled && self.results[thread.tx_idx].is_ok() {
            match next_transaction_option.clone() {
                Some(tx) => {
                    let new_thread = Thread::initialize_thread(tx, self.next_tx_idx);

                    self.next_threads.push(new_thread);
                    info!(
                        "    enqueued implicitly forked thread; queue size = {}",
                        self.next_threads.len()
                    );
                }
                None => {
                    info!("    no more transactionss to fork, skipping implicit fork.");
                }
            }
            self.next_tx_idx += 1;
        }
    }
}
