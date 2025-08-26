// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use log::trace;
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

type NextStmtMap = FxHashMap<StmtId, Option<StmtId>>;
type ArgMap<'a> = HashMap<&'a str, BitVecValue>;
type TodoItem = (String, Vec<BitVecValue>);
type TransactionInfo<'a> = (&'a Transaction, &'a SymbolTable, NextStmtMap);

/// The maximum number of iterations to run for convergence before breaking with an ExecutionLimitExceeded error
const MAX_ITERS: usize = 10000;

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
}

#[derive(Debug, Clone)]
pub struct Thread<'a> {
    pub todo: Todo<'a>,
    pub current_step: StmtId,
    pub next_step: Option<StmtId>,
    pub has_forked: bool,
    /// Index into the original `todos` and parallel `results` vector (used to store this thread's result)
    pub todo_idx: usize,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(todo: Todo<'a>, todo_idx: usize) -> Self {
        trace!(
            "Thread initialized with transaction: {:?}, thread_id={}",
            todo.tr.name,
            todo_idx
        );
        Self {
            current_step: todo.tr.body,
            next_step: None,
            todo_idx,
            todo,
            has_forked: false,
        }
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
    step_count: i32,
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

    pub fn new(
        transactions_and_symbols: Vec<(&'a Transaction, &'a SymbolTable)>,
        todos: Vec<TodoItem>,
        ctx: &'a Context,
        sys: &'a TransitionSystem,
        sim: Interpreter,
        handler: &'a mut DiagnosticHandler,
    ) -> Self {
        // Create irs with pre-computed next statement mappings
        let irs: Vec<TransactionInfo<'a>> = transactions_and_symbols
            .into_iter()
            .map(|(tr, st)| (tr, st, tr.next_stmt_mapping()))
            .collect();

        // setup the Evaluator and first Thread
        let initial_todo =
            Self::next_todo_helper(&todos, 0, &irs).expect("No transactions passed.");

        trace!(
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
        trace!("Added first thread to active_threads");
        Self {
            irs,
            todos,
            next_todo_idx: 1,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
            evaluator,
            results: vec![Ok(()); results_size],
            handler,
        }
    }

    pub fn execute_todos(&mut self) -> Vec<ExecutionResult<()>> {
        trace!(
            "\n==== Starting scheduling cycle {}, active threads: {} ====",
            self.step_count,
            self.active_threads.len()
        );

        while !self.active_threads.is_empty() {
            // initially there are no previous values. we always need to cycle at least twice to check convergence, and the first time we will get a previous input val.
            let mut previous_input_vals: Option<HashMap<SymbolId, InputValue>> = None;
            let mut active_input_vals: HashMap<SymbolId, InputValue>;

            // fixed point iteration with assertions off
            self.evaluator.disable_assertions_and_forks();

            let iters = 0;
            loop {
                // run every active thread up to the next step to synchronize on
                self.run_all_active_until_next_step();

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
                if iters > MAX_ITERS {
                    for thread in &self.active_threads {
                        self.results[thread.todo_idx] =
                            Err(ExecutionError::execution_limit_exceeded(MAX_ITERS));
                    }
                    // Emit diagnostics for all errors before returning
                    self.emit_all_diagnostics();
                    return self.results.clone();
                }

                print!("Active Input Vals {:?}", active_input_vals);

                // change the previous input vals to equal the active input vals
                previous_input_vals = Some(active_input_vals);
            }

            // achieved convergence, run one more time with assertions on
            trace!("Achieved Convergence. Running once more with assertions enabled...");
            self.evaluator.enable_assertions_and_forks();
            self.run_all_active_until_next_step();

            // now that all threads are synchronized on the step, we can run step() on the sim
            trace!("Stepping...");
            self.evaluator.sim_step();

            // Move each active thread into inactive or next
            while let Some(mut active_thread) = self.active_threads.pop() {
                let next_step: Option<StmtId> = active_thread.next_step;
                match next_step {
                    Some(next_step_id) => {
                        trace!(
                            "Thread with transaction {:?} reached step, moving to next_threads with step: {:?}",
                            active_thread.todo.tr.name, next_step_id
                        );

                        // if the thread is moving to next_threads, its current_step becomes its next_step and next_step becomes None
                        active_thread.current_step = next_step_id;
                        active_thread.next_step = None;
                        self.next_threads.push(active_thread)
                    }
                    None => {
                        trace!(
                            "Thread with transaction {:?} finished execution, moving to inactive_threads",
                            active_thread.todo.tr.name
                        );
                        self.inactive_threads.push(active_thread)
                    }
                }
            }

            // setup the threads for the next cycle
            if !self.next_threads.is_empty() {
                trace!(
                    "Moving {} threads from next_threads to active_threads for next cycle",
                    self.next_threads.len()
                );
                self.active_threads = std::mem::take(&mut self.next_threads);
                self.step_count += 1;
                trace!("Advancing to scheduling cycle: {}", self.step_count);
            } else {
                trace!("No more threads to schedule. Protocol execution complete.");
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

    pub fn run_all_active_until_next_step(&mut self) {
        for i in 0..self.active_threads.len() {
            self.run_thread_until_next_step(i);
        }
    }

    pub fn run_thread_until_next_step(&mut self, thread_idx: usize) {
        let next_todo_option = self.next_todo(self.next_todo_idx);
        let thread = &mut self.active_threads[thread_idx];
        let mut current = thread.current_step;

        trace!(
            "Running thread {} from step {:?}",
            thread.todo.tr.name,
            current
        );
        self.evaluator.context_switch(thread.todo.clone());

        // keep evaluating until we hit a Step, hit the end, or error out:
        loop {
            trace!("  Evaluating statement: {:?}", current);

            match self.evaluator.evaluate_stmt(&current) {
                // happy path: got a next statement
                Ok(Some(next_id)) => {
                    trace!(
                        "  Next statement: {:?} {:?}",
                        next_id,
                        thread.todo.tr[next_id]
                    );

                    match thread.todo.tr[next_id] {
                        Stmt::Step => {
                            trace!("  Step reached at {:?}, pausing.", next_id);
                            thread.next_step = Some(next_id);
                            return;
                        }

                        Stmt::Fork if self.evaluator.assertions_forks_enabled() => {
                            if thread.has_forked {
                                trace!(
                                    "  ERROR: Thread has already forked at this point, terminating thread"
                                );
                                let error = ExecutionError::double_fork(
                                    thread.todo_idx,
                                    thread.todo.tr.name.clone(),
                                    next_id,
                                );
                                self.results[thread.todo_idx] = Err(error);
                                thread.next_step = None;
                                return;
                            }
                            trace!("  Fork at {:?}, spawning new thread…", next_id);
                            match next_todo_option.clone() {
                                Some(todo) => {
                                    let new_thread =
                                        Thread::initialize_thread(todo, self.next_todo_idx);
                                    self.next_threads.push(new_thread);
                                    trace!(
                                        "    enqueued forked thread; queue size = {}",
                                        self.next_threads.len()
                                    );
                                }
                                None => {
                                    trace!("    no more todos to fork, skipping fork.");
                                }
                            }
                            self.next_todo_idx += 1;
                            // Mark this thread as having forked
                            trace!("  Marking thread {} as having forked.", { thread.todo_idx });
                            thread.has_forked = true;
                            // continue from the fork point
                            current = next_id;
                        }

                        _ => {
                            // default "just keep going" case
                            current = next_id;
                        }
                    }
                }

                // no more statements -> done
                Ok(None) => {
                    trace!("  Execution complete, no more statements.");
                    thread.next_step = None;
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    trace!("ERROR: {:?}, terminating thread", e);
                    self.results[thread.todo_idx] = Err(e);
                    thread.next_step = None;
                    break;
                }
            }
        }

        // fork if a thread has completed successfully
        // more specifically, if forks are enabled, and this thread has None for next_step, and the thread didn't fail
        if !thread.has_forked
            && self.evaluator.assertions_forks_enabled()
            && self.results[thread.todo_idx].is_ok()
        {
            match next_todo_option.clone() {
                Some(todo) => {
                    let new_thread = Thread::initialize_thread(todo, self.next_todo_idx);
                    self.next_threads.push(new_thread);
                    trace!(
                        "    enqueued implicitly forked thread; queue size = {}",
                        self.next_threads.len()
                    );
                }
                None => {
                    trace!("    no more todos to fork, skipping implicit fork.");
                }
            }
            self.next_todo_idx += 1;
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::errors::{AssertionError, EvaluationError, ExecutionError, ThreadError};
    use crate::setup::{assert_err, assert_ok, bv, setup_test_environment};

    macro_rules! assert_assertion_error {
        ($result:expr) => {
            match $result {
                Err(ExecutionError::Assertion(AssertionError::EqualityFailed { .. })) => {}
                other => panic!("Expected AssertionError, got: {:?}", other),
            }
        };
    }

    macro_rules! assert_thread_error {
        ($result:expr, $error_type:ident) => {
            match $result {
                Err(ExecutionError::Thread(ThreadError::$error_type { .. })) => {}
                other => panic!(
                    "Expected ThreadError::{}, got: {:?}",
                    stringify!($error_type),
                    other
                ),
            }
        };
    }

    #[test]
    fn test_scheduler_add() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/adders/adder_d1/add_d1.v",
            "tests/adders/adder_d1/add_d1.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // CASE 1: BOTH THREADS PASS
        let mut todos = vec![
            (String::from("add"), vec![bv(1, 32), bv(2, 32), bv(3, 32)]),
            (String::from("add"), vec![bv(4, 32), bv(5, 32), bv(9, 32)]),
        ];

        let sim = patronus::sim::Interpreter::new_with_wavedump(&ctx, &sys, "trace.fst");
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = bv(10, 32);
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[1]);

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = bv(4, 32);
        todos[1].1[2] = bv(9, 32);
        let sim3 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        assert_ok(&results[1]);
        assert_assertion_error!(&results[0]);

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = bv(10, 32);
        let sim4 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols,
            todos.clone(),
            &ctx,
            &sys,
            sim4,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[0]);
        assert_assertion_error!(&results[1]);
    }

    #[test]
    fn test_scheduler_mult() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/multipliers/mult_d2/mult_d2.v",
            "tests/multipliers/mult_d2/mult_d2.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // CASE 1: BOTH THREADS PASS
        let mut todos = vec![
            (String::from("mul"), vec![bv(1, 32), bv(2, 32), bv(2, 32)]),
            (String::from("mul"), vec![bv(6, 32), bv(8, 32), bv(48, 32)]),
        ];

        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = bv(47, 32);
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[1]);

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = bv(3, 32);
        todos[1].1[2] = bv(48, 32);
        let sim3 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        assert_ok(&results[1]);
        assert_assertion_error!(&results[0]);

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = bv(47, 32);
        let sim4 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols,
            todos.clone(),
            &ctx,
            &sys,
            sim4,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[0]);
        assert_assertion_error!(&results[1]);
    }

    #[test]
    fn test_scheduler_identity_d2_multiple_assign() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/identities/identity_d2/identity_d2.v",
            "tests/identities/identity_d2/identity_d2.prot",
            None,
            handler,
        );

        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // PASSING CASE: Single thread
        let mut todos = vec![(String::from("multiple_assign"), vec![bv(1, 32), bv(1, 32)])];
        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);

        // ERROR CASE: Two different assignments
        todos.push((String::from("multiple_assign"), vec![bv(2, 32), bv(2, 32)]));
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        match &results[0] {
            Err(ExecutionError::Thread(ThreadError::ConflictingAssignment {
                symbol_name, ..
            })) => {
                assert_eq!(symbol_name, "a");
            }
            other => panic!(
                "Expected ConflictingAssignment error for symbol 'a', got: {:?}",
                other
            ),
        }

        // PASSING CASE: Two assignments, but of same value (1)
        todos[1].1 = vec![bv(1, 32), bv(1, 32)];
        let sim3 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim3, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
    }

    #[test]
    fn test_scheduler_identity_d2_double_fork() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/identities/identity_d2/identity_d2.v",
            "tests/identities/identity_d2/identity_d2.prot",
            None,
            handler,
        );

        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // ERROR CASE: two_fork_err protocol
        let mut todos = vec![(String::from("two_fork_err"), vec![bv(1, 32), bv(1, 32)])];
        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        match &results[0] {
            Err(ExecutionError::Thread(ThreadError::DoubleFork {
                thread_idx: thread_id,
                ..
            })) => {
                assert_eq!(*thread_id, 0);
            }
            other => panic!("Expected DoubleFork error, got: {:?}", other),
        }

        // PASSING CASE: two_fork_ok protocol
        todos[0] = (String::from("two_fork_ok"), vec![bv(1, 32), bv(1, 32)]);
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
    }

    #[test]
    fn test_scheduler_identity_d1_implicit_fork() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/identities/identity_d1/identity_d1.v",
            "tests/identities/identity_d1/identity_d1.prot",
            None,
            handler,
        );

        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos = vec![
            (String::from("implicit_fork"), vec![bv(1, 32), bv(1, 32)]),
            (String::from("implicit_fork"), vec![bv(2, 32), bv(2, 32)]),
            (String::from("implicit_fork"), vec![bv(3, 32), bv(4, 32)]),
            (String::from("implicit_fork"), vec![bv(4, 32), bv(5, 32)]),
        ];
        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);
        assert_err(&results[2]);
        assert_ok(&results[3]);
        assert_assertion_error!(&results[2]);
    }

    #[test]
    fn test_scheduler_identity_d1_slicing() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/identities/identity_d1/identity_d1.v",
            "tests/identities/identity_d1/identity_d1.prot",
            None,
            handler,
        );

        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let mut todos = vec![
            (String::from("slicing_ok"), vec![bv(1, 32), bv(1, 32)]), // transaction: slicing_ok
            (String::from("slicing_invalid"), vec![bv(1, 32), bv(1, 32)]), // transaction: slicing_invalid
        ];
        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_err(&results[1]);

        // Check that the failure is InvalidSlice
        match &results[1] {
            Err(ExecutionError::Evaluation(EvaluationError::InvalidSlice { .. })) => {}
            other => panic!("Expected invalid slice failure, got: {:?}", other),
        }

        // test slices that will result in an error because the widths of the slices are different
        todos[1].0 = String::from("slicing_err"); // switch to running transaction slicing_err
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[1]);
    }

    #[test]
    fn test_scheduler_dual_identity() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/identities/dual_identity_d1/dual_identity_d1.v",
            "tests/identities/dual_identity_d1/dual_identity_d1.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // PASSING CASE: values of b agree
        let mut todos = vec![
            (String::from("one"), vec![bv(3, 64)]),
            (String::from("two"), vec![bv(2, 64), bv(3, 64)]),
        ];
        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);

        // FAILING CASE: values of b disagree
        todos[1].1 = vec![bv(2, 64), bv(5, 64)];
        let sim2 = patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_err(&results[1]);
        assert_assertion_error!(&results[1]);
    }

    #[test]
    fn test_scheduler_inverter() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/inverters/inverter_d0.v",
            "tests/inverters/inverter_d0.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos = vec![(String::from("invert"), vec![bv(0, 1), bv(1, 1)])];

        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_err(&results[0]);
        assert_thread_error!(&results[0], ConflictingAssignment);
    }

    #[test]
    fn test_scheduler_counter() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "tests/counters/counter.v",
            "tests/counters/counter.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos = vec![(String::from("count_up"), vec![bv(10, 64)])];

        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
    }

    #[test]
    fn test_scheduler_aes128() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "examples/tinyaes128/aes_128.v",
            "examples/tinyaes128/aes128.prot",
            Some("aes_128".to_string()),
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // Example taken from NIST FIPS 197
        let todos = vec![
            (
                String::from("aes128"),
                vec![
                    BitVecValue::from_u128(0x000102030405060708090a0b0c0d0e0f, 128), // key
                    BitVecValue::from_u128(0x00112233445566778899aabbccddeeff, 128), // state
                    BitVecValue::from_u128(0x69c4e0d86a7b0430d8cdb78070b4c55a, 128), // expected output
                ],
            ),
            (
                String::from("aes128"),
                vec![
                    BitVecValue::from_u128(0x00000000000000000000000000000000, 128), // key
                    BitVecValue::from_u128(0x00000000000000000000000000000000, 128), // state
                    BitVecValue::from_u128(0x66e94bd4ef8a2c3b884cfa59ca342b2e, 128), // expected output
                ],
            ),
        ];

        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results: Vec<Result<(), ExecutionError>> = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);
    }

    #[test]
    fn test_scheduler_register_file_write_read() {
        let handler = &mut DiagnosticHandler::new();
        let (parsed_data, ctx, sys) = setup_test_environment(
            "examples/serv/serv_regfile.v",
            "examples/serv/serv_regfile.prot",
            None,
            handler,
        );

        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos = vec![
            (
                String::from("read_write"),
                vec![
                    bv(0, 5),           // rs1_addr: u5
                    bv(0, 32),          // rs1_data: u32 (output)
                    bv(0, 32),          // rs2_data: u32 (output)
                    bv(0, 5),           // rs2_addr: u5
                    bv(1, 1),           // rd_enable: u1
                    bv(5, 5),           // rd_addr: u5
                    bv(0xdeadbeef, 32), // rd_data: u32
                    bv(0, 1),           // zero: u1
                    bv(1, 1),           // one: u1
                ],
            ),
            (
                String::from("read_write"),
                vec![
                    bv(5, 5),           // rs1_addr: u5
                    bv(0xdeadbeef, 32), // rs1_data: u32 (output)
                    bv(0, 32),          // rs2_data: u32 (output)
                    bv(0, 5),           // rs2_addr: u5
                    bv(0, 1),           // rd_enable: u1
                    bv(0, 5),           // rd_addr: u5
                    bv(0, 32),          // rd_data: u32
                    bv(0, 1),           // zero: u1
                    bv(1, 1),           // one: u1
                ],
            ),
        ];

        let sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_todos();
        assert_ok(&results[0]);
        assert_ok(&results[1]);
    }
}
