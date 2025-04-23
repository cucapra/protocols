// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
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
    args: &'a HashMap<&'a str, BitVecValue>,
}

impl<'a> Thread<'a> {
    pub fn initialize_thread(
        tr: &'a Transaction,
        st: &'a SymbolTable,
        step: StmtId,
        args: &'a HashMap<&str, BitVecValue>,
    ) -> Self {
        Self {
            tr,
            st,
            stepid: step,
            args,
        }
    }
}

pub struct Scheduler<'a> {
    transactions: &'a Vec<(&'a Transaction, &'a SymbolTable)>,
    fork_idx : usize,
    active_threads: Vec<Thread<'a>>,
    next_threads: Vec<Thread<'a>>,
    inactive_threads: Vec<Thread<'a>>,
    step_count: i32,
    evaluator: Evaluator<'a>,
}

impl<'a> Scheduler<'a> {
    pub fn new(
        transactions: &'a Vec<(&'a Transaction, &'a SymbolTable)>,
        step: StmtId,
        args: &'a HashMap<&'a str, BitVecValue>,
        ctx: &'a Context,
        sys: &'a TransitionSystem,
        sim: &'a mut Interpreter<'a>,
        handler: &'a mut DiagnosticHandler,
    ) -> Self {
        // Initialize sim
        // let (ctx, sys) = Evaluator::create_sim_context(verilog_path);
        // let mut sim: Interpreter<'_> = patronus::sim::Interpreter::new(&ctx, &sys);
        if (transactions.len() == 0){
            panic!("No transactions found in the system");
        }
        let (initial_tr, initial_st) = transactions[0];

        // Initialize evaluator with first transaction
        let evaluator = Evaluator::new(args.clone(), initial_tr, initial_st, handler, &ctx, &sys, sim);

        let first = Thread::initialize_thread(initial_tr, initial_st, step, args);
        Self {
            transactions,
            fork_idx: 0,
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
            evaluator,
        }
    }

    pub fn add_thread(
        &mut self,
        tr: &'a Transaction,
        st: &'a SymbolTable,
        step: StmtId,
        args: &'a HashMap<&str, BitVecValue>,
    ) {
        let new_thread = Thread::initialize_thread(&tr, &st, step, args);
        self.next_threads.push(new_thread);
    }

    pub fn schedule_threads(&mut self) {
        while self.active_threads.len() > 0 {
            let mut next_thread = self.active_threads.pop().unwrap();

            let next_step = self.run_thread_until_step(&next_thread);
            match next_step {
                Some(stepid) => {
                    next_thread.stepid = stepid;
                    self.next_threads.push(next_thread)
                }
                None => self.inactive_threads.push(next_thread),
            }
        }

        if self.next_threads.len() > 0 {
            self.active_threads = std::mem::take(&mut self.next_threads);
            self.step_count += 1;
        } else {
            println!("Finished running protocol")
        }
    }

    pub fn run_thread_until_step(&mut self, thread : &Thread<'a>) -> Option<StmtId> {
        self.evaluator.context_switch(thread.tr, thread.st, thread.args.clone());
        let mut current_step = Some(thread.stepid);

        while let Some(stepid) = current_step {
            let res = self.evaluator.evaluate_stmt(&stepid);

            match res {
                Ok(next_stmt_option) => {
                    match next_stmt_option {
                        Some(next_stmt_id) => {
                            match thread.tr[next_stmt_id] {
                                Stmt::Fork => {
                                    // Forking creates a new thread, so we need to add it to the next threads
                                    if (self.fork_idx >= self.transactions.len()){
                                        panic!("No more transactions to fork from");
                                    }
                                    else {
                                        self.fork_idx += 1;
                                        let tr = self.transactions[self.fork_idx].0;
                                        let st = self.transactions[self.fork_idx].1;
                                        let next_thread = Thread::initialize_thread(
                                            tr,
                                            st,
                                            next_stmt_id, // FIXME: this doesn't make sense if the fork goes to a new transaction
                                            thread.args,
                                        );
                                        self.next_threads.push(next_thread);
                                    }
                                }
                                Stmt::Step(_) => return Some(next_stmt_id),
                                _ => current_step = Some(next_stmt_id),
                            }
                        }
                        None => return None,
                    }
                }
                Err(e) => {
                    panic!("Error evaluating step: {:?}", e);
                }
            }
        }

        None
    }

}