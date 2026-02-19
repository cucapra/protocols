// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use baa::{BitVecOps, BitVecValue};
use log::info;
use rustc_hash::FxHashMap;

use crate::diagnostic::DiagnosticHandler;
use crate::errors::DiagnosticEmitter;
use crate::errors::{ExecutionError, ExecutionResult};
use crate::interpreter::{Evaluator, ThreadInputValue};
use crate::ir::*;

use patronus::expr::Context;
use patronus::sim::Interpreter;
use patronus::system::TransitionSystem;

/// `NextStmtMap` allows us to interpret without using recursion
/// (the interpreter can just lookup what the next statement is using this map)
pub type NextStmtMap = FxHashMap<StmtId, Option<StmtId>>;
type ArgMap<'a> = FxHashMap<&'a str, BitVecValue>;

/// A `TodoItem` corresponds to a function call in a transaction `.tx` file
pub type TodoItem = (String, Vec<BitVecValue>);

/// A `TransactionInfo` is a triple of the form
/// `(Transaction, SymbolTable, NextStmtMap)`.
/// This is passed to the interpreter when we want to execute
/// a single transaction.
type TransactionInfo<'a> = (&'a Transaction, &'a SymbolTable, NextStmtMap);

/// A `Todo` is a function call to be executed (i.e. a line in the `.tx` file)
#[derive(Debug, Clone)]
pub struct Todo<'a> {
    /// The associated `Transaction`
    pub tr: &'a Transaction,
    /// The associated `SymbolTable`
    pub st: &'a SymbolTable,
    /// The associated argument values (a map from variable names to their values)
    pub args: ArgMap<'a>,
    /// Maps each `StmtId` to an optional `StmtId` of the next statement
    pub next_stmt_map: NextStmtMap,

    /// Maps a `StmtId` pair to the no. of iterations remaining
    /// for that particular loop.              
    /// - **Invariant**: the no. of remaining iterations is always non-zero
    ///   (if it reaches zero, we remove the entry from this map).       
    /// - In the key, we need the `StmtId` to allow for nested loops,
    ///   and we also need the `TodoIdx`, since the same `StmtId` could be active
    ///   in differnt threads.
    pub bounded_loop_remaining_iters: FxHashMap<StmtId, u128>,
}

impl<'a> Todo<'a> {
    pub fn new(
        tr: &'a Transaction,
        st: &'a SymbolTable,
        args: ArgMap<'a>,
        next_stmt_map: NextStmtMap,
    ) -> Self {
        Self {
            tr,
            st,
            args,
            next_stmt_map,
            bounded_loop_remaining_iters: FxHashMap::default(),
        }
    }

    /// Pretty-prints a `Statement` based on its `StmtId`
    /// and the `SymbolTable` associated with this `Todo`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.tr.format_stmt(stmt_id, self.st)
    }
}

/// Struct containing metadata associated with a `Thread`
#[derive(Debug, Clone)]
pub struct Thread<'a> {
    /// The corresponding `Todo` (function call to be executed)
    pub todo: Todo<'a>,
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
    /// Index into the original `todos` and parallel `results` vector (used to store this thread's result)
    pub todo_idx: usize,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(todo: Todo<'a>, todo_idx: usize) -> Self {
        info!(
            "Thread initialized with transaction: {:?}, thread_id={}",
            todo.tr.name, todo_idx
        );
        Self {
            current_step: todo.tr.body,
            next_step: None,
            todo_idx,
            todo,
            prev_fork_stmt_id: None,
            has_stepped: false,
            has_forked: false,
        }
    }

    /// Pretty-prints a `Statement` identified by its `StmtId`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.todo.format_stmt(stmt_id)
    }

    /// Sets the next step and writes back bounded loop state from the evaluator.
    /// Called when thread execution pauses (at step, on error, or on completion).
    pub fn save_state(
        &mut self,
        next_step: Option<StmtId>,
        bounded_loop_remaining_iters: FxHashMap<StmtId, u128>,
    ) {
        self.next_step = next_step;
        self.todo.bounded_loop_remaining_iters = bounded_loop_remaining_iters;
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
    /// A `Vec` of `Transaction`s, along with their associated `SymbolTable`s
    /// and `NextStmtMap`s
    irs: Vec<TransactionInfo<'a>>,
    /// A list of `TodoItem`s to be executed (each element corresponds to
    /// a function call in a `.tx` file)
    todos: Vec<TodoItem>,
    /// The index of the next element in `todo`s to be executed when we `fork`
    next_todo_idx: usize,
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
}

impl<'a> Scheduler<'a> {
    // Helper method that creates a Todo struct
    fn next_todo_helper(
        todos: &[TodoItem],
        idx: usize,
        irs: &[TransactionInfo<'a>],
    ) -> Option<Todo<'a>> {
        if idx < todos.len() {
            // get the corresponding transaction, symbol table, and next_stmt_map
            let tr_name = todos[idx].0.clone();

            // find the ir corresponding to the transaction name
            let ir_idx = irs
                .iter()
                .position(|(tr, _, _)| tr.name == tr_name)
                .expect("Transaction not found in IRs");
            let (tr, st, next_stmt_map) = &irs[ir_idx];

            // setup the arguments for the transaction
            let args = todos[idx].1.clone();
            let mut args_map = FxHashMap::default();

            for (i, arg) in args.iter().enumerate() {
                let identifier = st[tr.args[i].symbol()].name();
                args_map.insert(identifier, arg.clone());
            }

            Some(Todo::new(tr, st, args_map, next_stmt_map.clone()))
        } else {
            None
        }
    }

    // Instance method that uses self fields and returns a Todo
    fn next_todo(&self, idx: usize) -> Option<Todo<'a>> {
        Self::next_todo_helper(&self.todos, idx, &self.irs)
    }

    /// Creates a new `Scheduler` struct and takes the following arguments:
    /// - A list of transactions and their associated symbol tables (`transactions_and_symbols`)
    /// - A list of function calls to execute (`todos`)
    /// - A Patronus context (`ctx`)
    /// - A Patronus transition system (`sys`)
    /// - A Patronus simulator (`sim`)
    /// - and a `DiagnosticHandler` for emitting errors (`handler`)
    pub fn new(
        transactions_and_symbols: Vec<(&'a Transaction, &'a SymbolTable)>,
        todos: Vec<TodoItem>,
        ctx: &'a Context,
        sys: &'a TransitionSystem,
        sim: Interpreter,
        handler: &'a mut DiagnosticHandler,
        max_steps: u32,
    ) -> Self {
        // Create irs with pre-computed next statement mappings
        let irs: Vec<TransactionInfo<'a>> = transactions_and_symbols
            .into_iter()
            .map(|(tr, st)| (tr, st, tr.next_stmt_mapping()))
            .collect();

        // setup the Evaluator and first Thread
        let initial_todo =
            Self::next_todo_helper(&todos, 0, &irs).expect("No transactions passed.");

        info!(
            "Starting with initial transaction: {:?}",
            initial_todo.tr.name
        );

        // Initialize evaluator with first transaction
        let evaluator = Evaluator::new(
            initial_todo.args.clone(),
            initial_todo.tr,
            initial_todo.st,
            ctx,
            sys,
            sim,
        );

        let results_size = todos.len();
        let first = Thread::initialize_thread(initial_todo, 0);

        info!("Added first thread to active_threads");
        Self {
            irs,
            todos,
            next_todo_idx: 1,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 0,
            evaluator,
            results: vec![Ok(()); results_size],
            handler,
            max_steps,
        }
    }

    /// Runs the scheduler on a list of `todo`s, returning a list of `ExecutionResult`s
    pub fn execute_todos(&mut self) -> Vec<ExecutionResult<()>> {
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
            self.evaluator.finalize_inputs_for_cycle();

            // Collect threads that need implicit forking (can't call self.next_todo during drain)
            let mut threads_needing_implicit_fork: Vec<usize> = Vec::new();

            // Move each active thread into inactive or next (drain preserves order)
            for mut active_thread in self.active_threads.drain(..) {
                let next_step: Option<StmtId> = active_thread.next_step;
                match next_step {
                    Some(next_step_id) => {
                        info!(
                            "Thread with transaction {:?} reached `Step()`, moving to next_threads with `Step()`: {:?}",
                            active_thread.todo.tr.name, next_step_id
                        );

                        // if the thread is moving to next_threads, its current_step becomes its next_step and next_step becomes None
                        active_thread.current_step = next_step_id;
                        active_thread.next_step = None;
                        self.next_threads.push(active_thread)
                    }
                    None => {
                        info!(
                            "Thread with transaction {:?} finished execution, moving to inactive_threads",
                            active_thread.todo.tr.name
                        );
                        // Clear thread inputs
                        self.evaluator.clear_thread_inputs(active_thread.todo_idx);

                        // Track if this thread needs implicit fork
                        if !active_thread.has_forked && self.results[active_thread.todo_idx].is_ok()
                        {
                            threads_needing_implicit_fork.push(active_thread.todo_idx);
                        }

                        self.inactive_threads.push(active_thread)
                    }
                }
            }

            // Process implicit forks after drain is complete
            for _todo_idx in threads_needing_implicit_fork {
                let next_todo_option = self.next_todo(self.next_todo_idx);
                match next_todo_option {
                    Some(todo) => {
                        let new_thread = Thread::initialize_thread(todo, self.next_todo_idx);
                        self.next_threads.push(new_thread);
                        info!(
                            "    enqueued implicitly forked thread; queue size = {}",
                            self.next_threads.len()
                        );
                    }
                    None => {
                        info!("    no more todos to fork, skipping implicit fork.");
                    }
                }
                self.next_todo_idx += 1;
            }

            // setup the threads for the next cycle
            if !self.next_threads.is_empty() {
                // advance simulation for next step
                info!("Stepping...");
                self.evaluator.sim_step();

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
                        self.results[thread.todo_idx] =
                            Err(ExecutionError::MaxStepsReached(self.max_steps));
                    }
                    // shut down execution by clearing all active threads
                    self.active_threads.clear();
                }
            } else {
                info!("No more threads to schedule. Protocol execution complete.");
            }
        }

        // Emit one trailing empty cycle so all generated .fst files having timing information
        self.evaluator.sim_step();

        // Emit diagnostics for all errors after execution is complete
        self.emit_all_diagnostics();
        self.results.clone()
    }

    /// Checks for conflicting assignments across all threads at end of cycle.
    /// Returns a list of (thread_idx, error) for each thread involved in a conflict.
    fn check_for_conflicts(&self) -> Vec<(usize, ExecutionError)> {
        let mut errors = Vec::new();
        let per_thread_input_vals = self.evaluator.per_thread_input_vals();
        // Safe to use any transaction's symbol table since all transactions must share
        // the same DUT struct symbols.
        let st = self.irs[0].1;

        for (symbol_id, per_thread_vals) in per_thread_input_vals {
            // Collect all concrete values with their thread indices and stmt_ids
            let concrete_vals: Vec<(usize, &BitVecValue, Option<StmtId>)> = per_thread_vals
                .iter()
                .filter_map(|(&todo_idx, (val, stmt_id))| {
                    if let ThreadInputValue::Concrete(bvv) = val {
                        Some((todo_idx, bvv, *stmt_id))
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
                        let symbol_name = st[*symbol_id].name().to_string();
                        let first_transaction_name = self.todos[*first_idx].0.clone();
                        let second_transaction_name = self.todos[*second_idx].0.clone();

                        // Error for first thread
                        errors.push((
                            *first_idx,
                            ExecutionError::conflicting_assignment(
                                *symbol_id,
                                symbol_name.clone(),
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
                                *symbol_id,
                                symbol_name,
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
        // results and todos are parallel arrays, so we can use the same idx
        for (idx, result) in self.results.iter().enumerate() {
            if let Err(error) = result {
                let ir_idx = self
                    .irs
                    .iter()
                    .position(|(tr, _, _)| tr.name == self.todos[idx].0.clone())
                    .expect("Transaction not found in IRs");
                let (tr, st, _) = self.irs[ir_idx];

                DiagnosticEmitter::emit_execution_error(self.handler, error, tr, st);
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
        let next_todo_option = self.next_todo(self.next_todo_idx);
        let thread = &mut self.active_threads[thread_idx];
        let mut current_stmt_id = thread.current_step;

        info!(
            "Running thread {} from `step()` ({})",
            thread.todo.tr.name, current_stmt_id
        );

        info!("  BEFORE context_switch");
        self.evaluator
            .context_switch(thread.todo.clone(), thread.todo_idx);
        info!("  AFTER context_switch");

        // Initialize thread inputs at cycle START (implicit reapplication)
        info!(
            "  About to call init_thread_inputs for todo_idx={} ({})",
            thread.todo_idx, thread.todo.tr.name
        );
        if let Err(e) = self.evaluator.init_thread_inputs(thread.todo_idx) {
            info!(
                "ERROR during init_thread_inputs: {:?}, terminating thread",
                e
            );
            self.results[thread.todo_idx] = Err(e);
            thread.save_state(None, self.evaluator.bounded_loop_remaining_iters());
            return;
        }

        // keep evaluating until we hit a Step, hit the end, or error out:
        loop {
            info!(
                "  Evaluating statement: `{}`",
                thread.format_stmt(&current_stmt_id)
            );

            match self.evaluator.evaluate_stmt(&current_stmt_id) {
                // happy path: got a next statement
                Ok(Some(next_id)) => {
                    info!(
                        "  Next statement: {:?} `{}`",
                        next_id,
                        thread.format_stmt(&next_id)
                    );

                    match thread.todo.tr[next_id] {
                        Stmt::Step => {
                            // We've encountered a step, so set `has_stepped` to true
                            if !thread.has_stepped {
                                thread.has_stepped = true;
                            }
                            info!("  `Step()` reached at {:?}, pausing.", next_id);

                            // Check if this is the final step (no statement after it)
                            // If so, thread completes at this cycle rather than running another useless cycle
                            let next_step =
                                if thread.todo.next_stmt_map.get(&next_id) == Some(&None) {
                                    info!("  This is the final step, thread completes.");
                                    None
                                } else {
                                    Some(next_id)
                                };
                            thread.save_state(
                                next_step,
                                self.evaluator.bounded_loop_remaining_iters(),
                            );
                            return;
                        }

                        Stmt::Fork if forks_enabled => {
                            if thread.has_forked {
                                info!(
                                    "  ERROR: Thread has already forked at this point, terminating thread"
                                );
                                let error = ExecutionError::double_fork(
                                    thread.todo_idx,
                                    thread.todo.tr.name.clone(),
                                    thread.prev_fork_stmt_id.expect("Forked multiple times but `prev_fork_stmt_id` field is `None`"),
                                    next_id,
                                );
                                self.results[thread.todo_idx] = Err(error);
                                thread.save_state(
                                    None,
                                    self.evaluator.bounded_loop_remaining_iters(),
                                );
                                return;
                            } else if !thread.has_stepped {
                                info!(
                                    "  ERROR: fork() called before step() in this thread, terminating thread"
                                );
                                thread.has_forked = true;
                                let error = ExecutionError::fork_before_step(
                                    thread.todo_idx,
                                    thread.todo.tr.name.clone(),
                                    next_id,
                                );
                                self.results[thread.todo_idx] = Err(error);
                                thread.save_state(
                                    None,
                                    self.evaluator.bounded_loop_remaining_iters(),
                                );
                                return;
                            }

                            info!("  `Fork` at stmt_id {}, spawning new thread…", next_id);
                            match next_todo_option.clone() {
                                Some(todo) => {
                                    let new_thread =
                                        Thread::initialize_thread(todo, self.next_todo_idx);

                                    self.next_threads.push(new_thread);
                                    info!(
                                        "    enqueued forked thread; queue size = {}",
                                        self.next_threads.len()
                                    );
                                }
                                None => {
                                    info!("    no more todos to fork, skipping fork.");
                                }
                            }
                            self.next_todo_idx += 1;
                            // Mark this thread as having forked
                            info!(
                                "  Marking thread {} (todo_idx {}) as having forked.",
                                thread.todo.tr.name, thread.todo_idx
                            );
                            // continue from the fork point
                            current_stmt_id = next_id;
                            // Update fields in the `Thread` struct that track whether
                            // we've forked already
                            thread.has_forked = true;
                            thread.prev_fork_stmt_id = Some(next_id);
                        }

                        _ => {
                            // default "just keep going" case
                            current_stmt_id = next_id;
                        }
                    }
                }

                // no more statements -> done
                Ok(None) => {
                    let thread_id = thread.todo_idx;
                    let transaction_name = thread.todo.tr.name.clone();

                    // Check if the last executed statement was `step()`
                    if let Stmt::Step = thread.todo.tr[current_stmt_id] {
                        // Thread completed execution successfully
                        // If the thread hasn't forked yet, implicit fork will happen below
                        info!("  Execution complete, no more statements.");
                    } else {
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
                    self.results[thread.todo_idx] = Err(e);
                    break;
                }
            }
        }
        // Save thread state after execution pauses (loop exited via break)
        thread.save_state(None, self.evaluator.bounded_loop_remaining_iters());

        // Clear this thread's inputs if it completed (before implicit fork so new thread starts fresh)
        if thread.next_step.is_none() {
            self.evaluator.clear_thread_inputs(thread.todo_idx);
        }

        // fork if a thread has completed successfully
        // more specifically, if forks are enabled, and this thread has None for next_step, and the thread didn't fail
        if !thread.has_forked && forks_enabled && self.results[thread.todo_idx].is_ok() {
            match next_todo_option.clone() {
                Some(todo) => {
                    let new_thread = Thread::initialize_thread(todo, self.next_todo_idx);

                    self.next_threads.push(new_thread);
                    info!(
                        "    enqueued implicitly forked thread; queue size = {}",
                        self.next_threads.len()
                    );
                }
                None => {
                    info!("    no more todos to fork, skipping implicit fork.");
                }
            }
            self.next_todo_idx += 1;
        }
    }
}
