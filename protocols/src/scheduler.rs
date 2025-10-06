// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use log::info;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

use crate::diagnostic::DiagnosticHandler;
use crate::errors::DiagnosticEmitter;
use crate::errors::{ExecutionError, ExecutionResult};
use crate::interpreter::Evaluator;
use crate::interpreter::InputValue;
use crate::ir::*;

use patronus::expr::Context;
use patronus::sim::Interpreter;
use patronus::system::TransitionSystem;

/// `NextStmtMap` allows us to interpret without using recursion
/// (the interpreter can just lookup what the next statement is using this map)
type NextStmtMap = FxHashMap<StmtId, Option<StmtId>>;
type ArgMap<'a> = HashMap<&'a str, BitVecValue>;

/// A `TodoItem` corresponds to a function call in a transaction `.tx` file
pub type TodoItem = (String, Vec<BitVecValue>);

/// We pass in `TransactionInfo` to the interpreter when we want to execute
/// a single statement
type TransactionInfo<'a> = (&'a Transaction, &'a SymbolTable, NextStmtMap);

/// The maximum number of iterations to run for convergence before breaking with an ExecutionLimitExceeded error
const MAX_ITERS: usize = 10000;

/// A `Todo` is a function call to be executed. The fields of this struct are:
/// - The associated `Transaction`
/// - The associated `SymbolTable`
/// - The associated argument values `args` (mapping variable names to their values)
/// - The `NextStmtMap`
#[derive(Debug, Clone)]
pub struct Todo<'a> {
    pub tr: &'a Transaction,
    pub st: &'a SymbolTable,
    pub args: ArgMap<'a>,
    pub next_stmt_map: NextStmtMap,
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
}

pub enum StepResult<'a> {
    /// Thread hit a Step and should be re-scheduled
    Continue(Thread<'a>),
    /// Thread ran to completion (no more statements)
    Completed(usize /* thread_id */),
    /// Thread errored out
    Error(usize /* thread_id */, ExecutionError),
}

pub struct Scheduler<'a> {
    irs: Vec<TransactionInfo<'a>>,
    todos: Vec<TodoItem>,
    /// Next index into `todos` to pull when we fork
    next_todo_idx: usize,
    active_threads: Vec<Thread<'a>>,
    next_threads: Vec<Thread<'a>>,
    inactive_threads: Vec<Thread<'a>>,
    step_count: u32,
    max_steps: u32,
    evaluator: Evaluator<'a>,
    results: Vec<ExecutionResult<()>>,
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
            let mut args_map = HashMap::new();

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
            // initially there are no previous values. we always need to cycle at least twice to check convergence, and the first time we will get a previous input val.
            let mut previous_input_vals: Option<HashMap<SymbolId, InputValue>> = None;
            let mut active_input_vals: HashMap<SymbolId, InputValue>;

            // fixed point iteration with assertions off
            self.evaluator.disable_assertions();

            let mut iters = 0;
            loop {
                // run every active thread up to the next step to synchronize on
                self.run_all_active_until_next_step(iters == 0); // only enable forks on the first iteration

                // if there are threads now in next_threads, we need to move them to active_threads
                if !self.next_threads.is_empty() {
                    info!(
                        "Moving {} threads from next_threads to active_threads",
                        self.next_threads.len()
                    );
                    self.active_threads.append(&mut self.next_threads);
                }

                // update the active input vals to reflect the current state
                // for each thread, get its current input_vals (read-only clone)
                active_input_vals = self.evaluator.input_vals();

                if let Some(prev_vals) = previous_input_vals {
                    if prev_vals == active_input_vals {
                        break;
                    }
                }

                // if we've exceeded the max number of iterations before convergence,
                // return an ExecutionLimitExceeded error on every thread.
                // we should be able to theoretically show convergence is always possible, however
                if iters > MAX_ITERS {
                    for thread in &self.active_threads {
                        self.results[thread.todo_idx] =
                            Err(ExecutionError::execution_limit_exceeded(MAX_ITERS));
                    }
                    // Emit diagnostics for all errors before returning
                    self.emit_all_diagnostics();
                    return self.results.clone();
                }

                info!("Active Input Vals {:?}", active_input_vals);

                // change the previous input vals to equal the active input vals
                previous_input_vals = Some(active_input_vals);

                iters += 1;
            }

            // achieved convergence, run one more time with assertions on
            info!("Achieved Convergence. Running once more with assertions enabled...");
            self.evaluator.enable_assertions();
            self.run_all_active_until_next_step(false);

            // now that all threads are synchronized on the step, we can run step() on the sim
            info!("Stepping...");
            self.evaluator.sim_step();

            // Move each active thread into inactive or next
            while let Some(mut active_thread) = self.active_threads.pop() {
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
                        self.inactive_threads.push(active_thread)
                    }
                }
            }

            // setup the threads for the next cycle
            if !self.next_threads.is_empty() {
                info!(
                    "Moving {} threads from next_threads to active_threads for next cycle",
                    self.next_threads.len()
                );
                self.active_threads = std::mem::take(&mut self.next_threads);
                self.step_count += 1;
                info!("Advancing to scheduling cycle: {}", self.step_count + 1);
                if self.step_count >= self.max_steps {
                    *(self.results.last_mut().unwrap()) =
                        Err(ExecutionError::MaxStepsReached(self.max_steps));
                    // shut down execution by clearing all active threads
                    self.active_threads.clear();
                }
            } else {
                info!("No more threads to schedule. Protocol execution complete.");
                info!("No more threads to schedule. Protocol execution complete.");
            }
        }

        // Emit diagnostics for all errors after execution is complete
        self.emit_all_diagnostics();
        self.results.clone()
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
        self.evaluator.context_switch(thread.todo.clone());

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
                            thread.next_step = Some(next_id);
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
                                thread.next_step = None;
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
                                thread.next_step = None;
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

                    // TODO: check if `thread.todo.tr[current_stmt_id]` is `Stmt::Step`
                    // (i.e. if the last executed statement was a `step()`)
                    if let Stmt::Step = thread.todo.tr[current_stmt_id] {
                        if forks_enabled && !thread.has_forked {
                            // Throw an error if forks are enabled but the
                            // thread finished without making any calls to `fork()`
                            info!(
                                "  ERROR: thread did not make any calls to `fork()`, terminating thread"
                            );
                            let error =
                                ExecutionError::finished_without_fork(thread_id, transaction_name);
                            self.results[thread_id] = Err(error);
                        } else {
                            info!("  Execution complete, no more statements.");
                        }
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
                    thread.next_step = None;
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    info!("ERROR: {:?}, terminating thread", e);
                    self.results[thread.todo_idx] = Err(e);
                    thread.next_step = None;
                    break;
                }
            }
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
