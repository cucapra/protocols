// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

use crate::diagnostic::DiagnosticHandler;
use crate::diagnostic::Level;
use crate::interpreter::Evaluator;
use crate::interpreter::InputValue;
use crate::ir::*;

use patronus::expr::Context;
use patronus::sim::Interpreter;
use patronus::system::TransitionSystem;

type NextStmtMap = FxHashMap<StmtId, Option<StmtId>>;
type ArgMap<'a> = HashMap<&'a str, BitVecValue>;
type TodoItem = (usize, Vec<BitVecValue>);
type TransactionInfo<'a> = (&'a Transaction, &'a SymbolTable, NextStmtMap);

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
    thread_id: usize,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(todo: Todo<'a>, thread_id: usize) -> Self {
        println!(
            "Thread initialized with transaction: {:?}, thread_id={}",
            todo.tr.name, thread_id
        );
        Self {
            current_step: todo.tr.body,
            next_step: None,
            thread_id,
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
    Error(usize /* thread_id */, String /* message */),
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
    results: Vec<Result<(), String>>,
}

impl<'a> Scheduler<'a> {
    // Helper method that creates a Todo struct
    fn create_todo_helper(
        todos: &[TodoItem],
        idx: usize,
        irs: &[TransactionInfo<'a>],
    ) -> Option<Todo<'a>> {
        if idx < todos.len() {
            // get the corresponding transaction, symbol table, and next_stmt_map
            let ir_idx = todos[idx].0;
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
        Self::create_todo_helper(&self.todos, idx, &self.irs)
    }

    pub fn new(
        transactions_and_symbols: Vec<(&'a Transaction, &'a SymbolTable)>,
        todos: Vec<TodoItem>,
        ctx: &'a Context,
        sys: &'a TransitionSystem,
        sim: &'a mut Interpreter<'a>,
        handler: &'a mut DiagnosticHandler,
    ) -> Self {
        // Create irs with pre-computed next statement mappings
        let irs: Vec<TransactionInfo<'a>> = transactions_and_symbols
            .into_iter()
            .map(|(tr, st)| (tr, st, tr.next_stmt_mapping()))
            .collect();

        // setup the Evaluator and first Thread
        let next_todo_idx = 0;
        let initial_todo =
            Self::create_todo_helper(&todos, next_todo_idx, &irs).expect("No transactions passed.");

        println!(
            "Starting with initial transaction: {:?}",
            initial_todo.tr.name
        );

        // Initialize evaluator with first transaction
        let evaluator = Evaluator::new(
            initial_todo.args.clone(),
            initial_todo.tr,
            initial_todo.st,
            handler,
            ctx,
            sys,
            sim,
        );

        let results_size = todos.len();
        let first = Thread::initialize_thread(initial_todo, next_todo_idx);
        println!("Added first thread to active_threads");
        Self {
            irs,
            todos,
            next_todo_idx,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
            evaluator,
            results: vec![Ok(()); results_size],
        }
    }

    pub fn execute_threads(&mut self) -> Vec<Result<(), String>> {
        println!(
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

                print!("Active Input Vals {:?}", active_input_vals);

                // change the previous input vals to equal the active input vals
                previous_input_vals = Some(active_input_vals);
            }

            // achieved convergence, run one more time with assertions on
            println!("Achieved Convergence. Running once more with assertions enabled...");
            self.evaluator.enable_assertions_and_forks();
            self.run_all_active_until_next_step();

            // now that all threads are synchronized on the step, we can run step() on the sim
            println!("Stepping...");
            self.evaluator.sim_step();

            // Move each active thread into inactive or next
            while let Some(mut active_thread) = self.active_threads.pop() {
                let next_step: Option<StmtId> = active_thread.next_step;
                match next_step {
                    Some(next_step_id) => {
                        println!(
                            "Thread with transaction {:?} reached step, moving to next_threads with step: {:?}",
                            active_thread.todo.tr.name, next_step_id
                        );

                        // if the thread is moving to next_threads, its current_step becomes its next_step and next_step becomes None
                        active_thread.current_step = next_step_id;
                        active_thread.next_step = None;
                        self.next_threads.push(active_thread)
                    }
                    None => {
                        println!(
                            "Thread with transaction {:?} finished execution, moving to inactive_threads",
                            active_thread.todo.tr.name
                        );
                        self.inactive_threads.push(active_thread)
                    }
                }
            }

            // setup the threads for the next cycle
            if !self.next_threads.is_empty() {
                println!(
                    "Moving {} threads from next_threads to active_threads for next cycle",
                    self.next_threads.len()
                );
                self.active_threads = std::mem::take(&mut self.next_threads);
                self.step_count += 1;
                println!("Advancing to scheduling cycle: {}", self.step_count);
            } else {
                println!("No more threads to schedule. Protocol execution complete.");
            }
        }

        self.results.clone()
    }

    pub fn run_all_active_until_next_step(&mut self) {
        for i in 0..self.active_threads.len() {
            self.run_thread_until_next_step(i);
        }
    }

    pub fn run_thread_until_next_step(&mut self, thread_idx: usize) {
        let next_todo_option = self.next_todo(self.next_todo_idx + 1);
        let thread = &mut self.active_threads[thread_idx];
        let mut current = thread.current_step;

        println!(
            "Running thread {} from step {:?}",
            thread.todo.tr.name, current
        );
        self.evaluator.context_switch(thread.todo.clone());

        // keep evaluating until we hit a Step, hit the end, or error out:
        loop {
            println!("  Evaluating statement: {:?}", current);

            match self.evaluator.evaluate_stmt(&current) {
                // happy path: got a next statement
                Ok(Some(next_id)) => {
                    println!(
                        "  Next statement: {:?} {:?}",
                        next_id, thread.todo.tr[next_id]
                    );

                    match thread.todo.tr[next_id] {
                        Stmt::Step => {
                            println!("  Step reached at {:?}, pausing.", next_id);
                            thread.next_step = Some(next_id);
                            return;
                        }

                        Stmt::Fork if self.evaluator.assertions_forks_enabled() => {
                            if thread.has_forked {
                                println!("  ERROR: Thread has already forked at this point, terminating thread");
                                let msg = "Double Fork: Thread attempted to fork more than once";
                                self.evaluator.handler.emit_diagnostic_stmt(
                                    thread.todo.tr,
                                    &current,
                                    msg,
                                    Level::Error,
                                );
                                self.results[thread.thread_id] = Err(msg.to_string());
                                thread.next_step = None;
                            }
                            println!("  Fork at {:?}, spawning new thread…", next_id);
                            self.next_todo_idx += 1;
                            match next_todo_option.clone() {
                                Some(todo) => {
                                    let new_thread =
                                        Thread::initialize_thread(todo, self.next_todo_idx);
                                    self.next_threads.push(new_thread);
                                    println!(
                                        "    enqueued forked thread; queue size = {}",
                                        self.next_threads.len()
                                    );
                                }
                                None => {
                                    println!("    no more todos to fork, skipping fork.");
                                }
                            }
                            // Mark this thread as having forked
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
                    println!("  Execution complete, no more statements.");
                    thread.next_step = None;
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    println!("ERROR: {:?}, terminating thread", e);
                    self.results[thread.thread_id] = Err(e);
                    thread.next_step = None;
                    break;
                }
            }
        }

        // fork if a thread has completed successfully
        // more specically, if forks are enabled, and this thread has None for next_step, and the thread didn't fail
        if !thread.has_forked
            && self.evaluator.assertions_forks_enabled()
            && self.results[thread.thread_id].is_ok()
        {
            self.next_todo_idx += 1;
            match next_todo_option.clone() {
                Some(todo) => {
                    let new_thread = Thread::initialize_thread(todo, self.next_todo_idx);
                    self.next_threads.push(new_thread);
                    println!(
                        "    enqueued forked thread; queue size = {}",
                        self.next_threads.len()
                    );
                }
                None => {
                    println!("    no more todos to fork, skipping fork.");
                }
            }
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::parser::parsing_helper;
    use crate::yosys::yosys_to_btor;
    use crate::yosys::ProjectConf;
    use crate::yosys::YosysEnv;
    use std::path::PathBuf;

    fn create_sim_context(
        verilog_path: &str,
    ) -> (patronus::expr::Context, patronus::system::TransitionSystem) {
        // Verilog --> Btor via Yosys
        let env = YosysEnv::default();
        let inp = PathBuf::from(verilog_path);
        let proj = ProjectConf::with_source(inp);
        let btor_file = yosys_to_btor(&env, &proj, None).unwrap();

        // instantiate sim from btor file
        let (ctx, sys) = match patronus::btor2::parse_file(btor_file.as_path().as_os_str()) {
            Some(result) => result,
            None => {
                panic!("Failed to parse btor file.");
            }
        };
        (ctx, sys)
    }

    #[test]
    fn test_scheduler_add() {
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/add_struct.prot";
        let verilog_path = "examples/adders/add_d1.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // CASE 1: BOTH THREADS PASS
        let mut todos: Vec<(usize, Vec<BitVecValue>)> = vec![
            (
                0,
                vec![
                    BitVecValue::from_u64(1, 32),
                    BitVecValue::from_u64(2, 32),
                    BitVecValue::from_u64(3, 32),
                ],
            ),
            (
                0,
                vec![
                    BitVecValue::from_u64(4, 32),
                    BitVecValue::from_u64(5, 32),
                    BitVecValue::from_u64(9, 32),
                ],
            ),
        ];

        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(10, 32);
        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = BitVecValue::from_u64(4, 32);
        todos[1].1[2] = BitVecValue::from_u64(9, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_ok());

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(10, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols,
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_err());
    }

    #[test]
    fn test_scheduler_mult() {
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/mult_new.prot";
        let verilog_path = "examples/multipliers/mult_d2.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // CASE 1: BOTH THREADS PASS
        let mut todos: Vec<(usize, Vec<BitVecValue>)> = vec![
            (
                0,
                vec![
                    BitVecValue::from_u64(1, 32),
                    BitVecValue::from_u64(2, 32),
                    BitVecValue::from_u64(2, 32),
                ],
            ),
            (
                0,
                vec![
                    BitVecValue::from_u64(6, 32),
                    BitVecValue::from_u64(8, 32),
                    BitVecValue::from_u64(48, 32),
                ],
            ),
        ];

        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(47, 32);
        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = BitVecValue::from_u64(3, 32);
        todos[1].1[2] = BitVecValue::from_u64(48, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_ok());

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(47, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(
            transactions_and_symbols,
            todos.clone(),
            &ctx,
            &sys,
            sim3,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_err());
    }

    #[test]
    fn test_scheduler_identity_d2_multiple_assign() {
        // we expect this to fail due to the value being reassigned multiple times
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/identities/identity_d2.prot";
        let verilog_path = "examples/identity/identity_d2.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // PASSING CASE: Single thread
        let mut todos: Vec<(usize, Vec<BitVecValue>)> = vec![(
            0,
            vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)],
        )];
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());

        // ERROR CASE: Two different assigments
        todos.push((
            0,
            vec![BitVecValue::from_u64(2, 32), BitVecValue::from_u64(2, 32)],
        ));

        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_threads();
        // this should fail due to both threads trying to assign to the same input
        assert!(results[0].is_err());
        if let Err(err_msg) = &results[0] {
            assert_eq!(
                err_msg,
                "Multiple threads attempting to assign to the same input: a"
            );
        }

        // PASSING CASE: Two assignments, but of same value (1)
        todos[1].1 = vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)];

        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_threads();
        // this should fail due to both threads trying to assign to the same input
        assert!(results[0].is_ok());
    }

    #[test]
    fn test_scheduler_identity_d2_double_fork() {
        // we expect this to fail due to the value being reassigned multiple times
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/identities/identity_d2.prot";
        let verilog_path = "examples/identity/identity_d2.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // ERROR CASE: two_fork_err protocol
        let mut todos: Vec<(usize, Vec<BitVecValue>)> = vec![(
            1,
            vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)],
        )];
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        if let Err(err_msg) = &results[0] {
            assert_eq!(
                err_msg,
                "Double Fork: Thread attempted to fork more than once"
            );
        }

        // PASSING CASE: two_fork_ok protocol
        todos[0] = (
            2,
            vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)],
        );

        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
    }

    #[test]
    fn test_scheduler_identity_d1_implicit_fork() {
        // we expect this to fail due to the value being reassigned multiple times
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/identities/identity_d1.prot";
        let verilog_path = "examples/identity/identity_d1.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos: Vec<(usize, Vec<BitVecValue>)> = vec![
            (
                0,
                vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)],
            ),
            (
                0,
                vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(2, 32)],
            ),
            (
                0,
                vec![BitVecValue::from_u64(2, 32), BitVecValue::from_u64(3, 32)],
            ),
        ];
        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());
        assert!(results[2].is_err());
    }

    #[test]
    fn test_scheduler_dual_identity() {
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/identities/dual_identity_d1.prot";
        let verilog_path = "examples/identity/dual_identity_d1.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // PASSING CASE: values of b agree
        // whether this converges after one or two iterations is dependent on the scheduling order, but it should converge nonetheless
        let mut todos: Vec<(usize, Vec<BitVecValue>)> = vec![
            (0, vec![BitVecValue::from_u64(3, 64)]),
            (
                1,
                vec![BitVecValue::from_u64(2, 64), BitVecValue::from_u64(3, 64)],
            ),
        ];
        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // FAILING CASE: values of b disagree
        todos[1].1 = vec![BitVecValue::from_u64(2, 64), BitVecValue::from_u64(5, 64)];
        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);
        scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim2,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());
    }

    #[test]
    fn test_scheduler_inverter() {
        // we expect this to fail due to the value being reassigned multiple times
        let handler = &mut DiagnosticHandler::new();

        // test_helper("tests/add_struct.prot", "add_struct");
        let transaction_filename = "tests/inverter.prot";
        let verilog_path = "examples/inverters/inverter_d0.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let transactions_and_symbols: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos: Vec<(usize, Vec<BitVecValue>)> = vec![(
            0,
            vec![BitVecValue::from_u64(0, 1), BitVecValue::from_u64(1, 1)],
        )];

        let mut scheduler = Scheduler::new(
            transactions_and_symbols.clone(),
            todos.clone(),
            &ctx,
            &sys,
            sim,
            handler,
        );
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
    }

    #[test]
    fn test_empty() {
        // vacuous test where the protocol has no statements in it (just an empty block)
        // all results should always be ok, regardless of inputs.
        let handler = &mut DiagnosticHandler::new();
        let transaction_filename = "tests/identities/empty.prot";
        let verilog_path = "examples/identity/identity_d0.v";
        let (ctx, sys) = create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        let todos: Vec<(usize, Vec<BitVecValue>)> = vec![(
            0,
            vec![BitVecValue::from_u64(0, 32), BitVecValue::from_u64(1, 32)],
            
        ),
        (
            0,
            vec![BitVecValue::from_u64(1, 32), BitVecValue::from_u64(1, 32)],
        ),
        (
            0,
            vec![BitVecValue::from_u64(0, 32), BitVecValue::from_u64(1, 32)],
        )];

        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results: Vec<Result<(), String>> = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());
        assert!(results[2].is_ok());
    }
}
