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
    pub stepid: StmtId,
    args: HashMap<&'a str, BitVecValue>,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(
        tr: &'a Transaction,
        st: &'a SymbolTable,
        args: HashMap<&'a str, BitVecValue>,
    ) -> Self {
        println!("Thread initialized with transaction: {:?}", tr.name);
        Self {
            tr,
            st,
            stepid: tr.body,
            args,
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
        let res = Self::next_ir(todos.clone(), 0, irs.clone());
        if res.is_none() {
            panic!("No transactions found in the system");
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

        let first = Thread::initialize_thread(initial_tr, initial_st, initial_args);
        println!("Added first thread to active_threads");
        Self {
            irs,
            todos,
            fork_idx: 0,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
            evaluator,
        }
    }

    fn next_ir(
        todos: Vec<(usize, Vec<BitVecValue>)>,
        idx: usize,
        irs: Vec<(&'a Transaction, &'a SymbolTable)>,
    ) -> Option<(
        &'a Transaction,
        &'a SymbolTable,
        HashMap<&'a str, BitVecValue>,
    )> {
        if idx < irs.len() {
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

    pub fn schedule_threads(&mut self) {
        println!(
            "\n==== Starting scheduling cycle {}, active threads: {} ====",
            self.step_count,
            self.active_threads.len()
        );
        while self.active_threads.len() > 0 {
            let mut next_thread = self.active_threads.pop().unwrap();
            println!(
                "Processing thread with transaction: {:?}, step: {:?}",
                next_thread.tr.name, next_thread.stepid
            );

            let next_step = self.run_thread_until_step(&next_thread);
            match next_step {
                Some(stepid) => {
                    next_thread.stepid = stepid;
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
    }

    pub fn run_thread_until_step(&mut self, thread: &Thread<'a>) -> Option<StmtId> {
        println!(
            "Running thread with transaction: {:?} from step: {:?}",
            thread.tr.name, thread.stepid
        );
        self.evaluator
            .context_switch(thread.tr, thread.st, thread.args.clone());
        let mut current_step = Some(thread.stepid);

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
                                Stmt::Step(_) => {
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
                                    if let Some((tr, st, args)) = Self::next_ir(
                                        self.todos.clone(),
                                        self.fork_idx,
                                        self.irs.clone(),
                                    ) {
                                        println!(
                                            "  Forking new thread with transaction: {:?}",
                                            tr.name
                                        );
                                        let next_thread = Thread::initialize_thread(tr, st, args);
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
                    println!("ERROR evaluating step: {:?}", e);
                    panic!("Error evaluating step: {:?}", e);
                }
            }
        }

        println!("Thread execution complete");
        None
    }
}
