// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use std::collections::HashMap;

use crate::diagnostic::DiagnosticHandler;
use crate::interpreter::Evaluator;
use crate::ir::*;
use patronus::expr::Context;
use patronus::sim::Interpreter;
use patronus::system::TransitionSystem;

#[derive(Debug, Clone)]
pub struct Thread<'a> {
    pub tr: &'a Transaction,
    pub st: &'a SymbolTable,
    pub current_stmt: StmtId,
    args: HashMap<&'a str, BitVecValue>,
    /// The current index of the most recent todo that has been forked
    /// (a thread is or was running it).
    fork_idx: usize,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(
        tr: &'a Transaction,
        st: &'a SymbolTable,
        args: HashMap<&'a str, BitVecValue>,
        fork_idx: usize,
    ) -> Self {
        println!("Thread initialized with transaction: {:?}", tr.name);
        Self {
            tr,
            st,
            current_stmt: tr.body,
            args,
            fork_idx,
        }
    }
}

pub struct Scheduler<'a> {
    irs: Vec<(&'a Transaction, &'a SymbolTable)>,
    todos: Vec<(usize, Vec<BitVecValue>)>,
    fork_idx: usize,
    active_threads: Vec<Thread<'a>>,
    next_threads: Vec<Thread<'a>>,
    inactive_threads: Vec<Thread<'a>>,
    step_count: i32,
    evaluator: Evaluator<'a>,
    results: Vec<Result<(), String>>,
}

impl<'a> Scheduler<'a> {
    pub fn new(
        irs: Vec<(&'a Transaction, &'a SymbolTable)>,
        todos: Vec<(usize, Vec<BitVecValue>)>,
        ctx: &'a Context,
        sys: &'a TransitionSystem,
        sim: &'a mut Interpreter<'a>,
        handler: &'a mut DiagnosticHandler,
    ) -> Self {
        let res = Self::next_ir(&todos, 0, irs.clone());
        if res.is_none() {
            panic!("No transactions passed.");
        }
        let (initial_tr, initial_st, initial_args) = res.unwrap();

        println!("Starting with initial transaction: {:?}", initial_tr.name);

        // Initialize evaluator with first transaction
        let evaluator = Evaluator::new(
            initial_args.clone(),
            &initial_tr,
            &initial_st,
            handler,
            &ctx,
            &sys,
            sim,
        );

        let fork_idx = 0;
        let results_size = todos.len();
        let first = Thread::initialize_thread(initial_tr, initial_st, initial_args, fork_idx);
        println!("Added first thread to active_threads");
        Self {
            irs,
            todos,
            fork_idx,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
            evaluator,
            results: vec![Ok(()); results_size],
        }
    }

    fn next_ir(
        todos: &Vec<(usize, Vec<BitVecValue>)>,
        idx: usize,
        irs: Vec<(&'a Transaction, &'a SymbolTable)>,
    ) -> Option<(
        &'a Transaction,
        &'a SymbolTable,
        HashMap<&'a str, BitVecValue>,
    )> {
        if idx < todos.len() {
            // get the corresponding transaction and symbol table
            let (tr, st) = irs[todos[idx].0];

            // setup the arguments for the transaction
            let args = todos[idx].1.clone();
            let mut args_map = HashMap::new();

            for (i, arg) in args.iter().enumerate() {
                let identifier = st[tr.args[i].symbol()].name();
                args_map.insert(identifier, arg.clone());
            }

            Some((tr, st, args_map))
        } else {
            None
        }
    }

    pub fn execute_threads(&mut self) -> Vec<Result<(), String>> {
        println!(
            "\n==== Starting scheduling cycle {}, active threads: {} ====",
            self.step_count,
            self.active_threads.len()
        );
        while self.active_threads.len() > 0 {
            let mut next_thread = self.active_threads.pop().unwrap();
            println!(
                "Processing thread with transaction: {:?}, step: {:?}",
                next_thread.tr.name, next_thread.current_stmt
            );

            let next_step = self.run_thread_until_step(&next_thread);
            match next_step {
                Some(stepid) => {
                    next_thread.current_stmt = stepid;
                    println!("Thread with transaction {:?} reached step, moving to next_threads with step: {:?}", 
                            next_thread.tr.name, stepid);
                    self.next_threads.push(next_thread)
                }
                None => {
                    println!("Thread with transaction {:?} finished execution, moving to inactive_threads", 
                            next_thread.tr.name);
                    self.inactive_threads.push(next_thread)
                }
            }

            if self.next_threads.len() > 0 {
                println!(
                    "Moving {} threads from next_threads to active_threads for next cycle",
                    self.next_threads.len()
                );
                self.active_threads = std::mem::take(&mut self.next_threads);
                self.step_count += 1;
                println!("Advancing to scheduling cycle: {}", self.step_count);
            } else {
                println!("No more threads to schedule. Protocol execution complete.");
                println!("Total inactive threads: {}", self.inactive_threads.len());
            }

            // now that all threads are synchronized on the step, we can run step() on the sim
            self.evaluator.sim_step();
        }

        return self.results.clone();
    }

    pub fn run_thread_until_step(&mut self, thread: &Thread<'a>) -> Option<StmtId> {
        println!(
            "Running thread with transaction: {:?} from current_stmt: {:?}",
            thread.tr.name, thread.current_stmt
        );
        self.evaluator
            .context_switch(thread.tr, thread.st, thread.args.clone());
        let mut current_step = Some(thread.current_stmt);

        while let Some(stepid) = current_step {
            println!("  Evaluating statement: {:?}", stepid);
            let res = self.evaluator.evaluate_stmt(&stepid);

            match res {
                Ok(next_stmt_option) => {
                    match next_stmt_option {
                        Some(next_stmt_id) => {
                            println!(
                                "  Next statement: {:?}, type: {:?}",
                                next_stmt_id, &thread.tr[next_stmt_id]
                            );
                            match thread.tr[next_stmt_id] {
                                // if a step, stop execution
                                Stmt::Step => {
                                    println!(
                                        "  Step reached, thread will pause at: {:?}",
                                        next_stmt_id
                                    );
                                    return Some(next_stmt_id);
                                }

                                // if a fork, fork and continue execution
                                Stmt::Fork => {
                                    println!("  Fork reached at statement: {:?}", next_stmt_id);
                                    // Forking creates a new thread, so we need to add it to the next threads

                                    self.fork_idx += 1;
                                    if let Some((tr, st, args)) =
                                        Self::next_ir(&self.todos, self.fork_idx, self.irs.clone())
                                    {
                                        println!(
                                            "  Forking new thread with transaction: {:?}",
                                            tr.name
                                        );
                                        let next_thread =
                                            Thread::initialize_thread(tr, st, args, self.fork_idx);
                                        self.next_threads.push(next_thread);
                                        println!("  Forked thread added to next_threads queue. Queue size: {}", 
                                        self.next_threads.len());
                                    } else {
                                        println!("  No more irs to fork, continuing execution");
                                    }

                                    current_step = Some(next_stmt_id); // this thread keeps running
                                }

                                // if anything else, continue execution
                                _ => {
                                    println!(
                                        "  Continuing execution to next statement: {:?}",
                                        next_stmt_id
                                    );
                                    current_step = Some(next_stmt_id)
                                }
                            }
                        }
                        None => {
                            println!("  Thread execution complete, no more statements");
                            return None;
                        }
                    }
                }
                Err(e) => {
                    println!(
                        "ERROR evaluating statement, ending threead execution: {:?}",
                        e
                    );
                    self.results[thread.fork_idx] = Err(e);
                    return None;
                }
            }
        }
        None
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::parser::parsing_helper;

    #[test]
    fn test_scheduler_add() {
        let handler = &mut DiagnosticHandler::new();

        // test_helper("tests/add_struct.prot", "add_struct");
        let transaction_filename = "tests/add_struct.prot";
        let verilog_path = "examples/adders/add_d1.v";
        let (ctx, sys) = Evaluator::create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
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

        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(10, 32);
        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = BitVecValue::from_u64(4, 32);
        todos[1].1[2] = BitVecValue::from_u64(9, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim3, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_ok());

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(10, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs, todos.clone(), &ctx, &sys, sim3, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_err());
    }

    #[test]
    fn test_scheduler_mult() {
        let handler = &mut DiagnosticHandler::new();

        // test_helper("tests/add_struct.prot", "add_struct");
        let transaction_filename = "tests/mult_new.prot";
        let verilog_path = "examples/multipliers/mult_d2.v";
        let (ctx, sys) = Evaluator::create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
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

        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(47, 32);
        let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_err());

        // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        todos[0].1[2] = BitVecValue::from_u64(3, 32);
        todos[1].1[2] = BitVecValue::from_u64(48, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim3, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_ok());

        // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        todos[1].1[2] = BitVecValue::from_u64(47, 32);
        let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        scheduler = Scheduler::new(irs, todos.clone(), &ctx, &sys, sim3, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_err());
        assert!(results[1].is_err());
    }

    // TODO: Run two different transactions on the same DUT

    #[ignore]
    #[test]
    fn test_scheduler_simple_if() {
        let handler = &mut DiagnosticHandler::new();

        // test_helper("tests/add_struct.prot", "add_struct");
        let transaction_filename = "tests/simple_if.prot";
        let verilog_path = "examples/counter/counter.v";
        let (ctx, sys) = Evaluator::create_sim_context(verilog_path);
        let sim = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // FIXME: This is very unweildy, but once we move to owned transactions, we can get rid of this
        let parsed_data: Vec<(Transaction, SymbolTable)> =
            parsing_helper(transaction_filename, handler);
        let irs: Vec<(&Transaction, &SymbolTable)> =
            parsed_data.iter().map(|(tr, st)| (tr, st)).collect();

        // CASE 1: BOTH THREADS PASS
        let todos: Vec<(usize, Vec<BitVecValue>)> = vec![
            (
                0,
                vec![BitVecValue::from_u64(32, 64), BitVecValue::from_u64(7, 64)],
            ),
            (
                0,
                vec![BitVecValue::from_u64(31, 32), BitVecValue::from_u64(1, 32)],
            ),
        ];

        let mut scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim, handler);
        let results = scheduler.execute_threads();
        assert!(results[0].is_ok());
        assert!(results[1].is_ok());

        // CASE 2: FIRST THREAD PASSES, SECOND THREAD FAILS
        // todos[1].1[2] = BitVecValue::from_u64(47, 32);
        // let sim2 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim2, handler);
        // let results = scheduler.execute_threads();
        // assert!(results[0].is_ok());
        // assert!(results[1].is_err());

        // // CASE 3: FIRST THREAD FAILS, SECOND THREAD PASSES
        // todos[0].1[2] = BitVecValue::from_u64(3, 32);
        // todos[1].1[2] = BitVecValue::from_u64(48, 32);
        // let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // scheduler = Scheduler::new(irs.clone(), todos.clone(), &ctx, &sys, sim3, handler);
        // let results = scheduler.execute_threads();
        // assert!(results[0].is_err());
        // assert!(results[1].is_ok());

        // // CASE 4: FIRST THREAD FAILS, SECOND THREAD FAILS
        // todos[1].1[2] = BitVecValue::from_u64(47, 32);
        // let sim3 = &mut patronus::sim::Interpreter::new(&ctx, &sys);

        // scheduler = Scheduler::new(irs, todos.clone(), &ctx, &sys, sim3, handler);
        // let results = scheduler.execute_threads();
        // assert!(results[0].is_err());
        // assert!(results[1].is_err());
    }
}
