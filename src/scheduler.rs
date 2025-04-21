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
    pub transaction: &'a Transaction,
    pub symbol_table: &'a SymbolTable,
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
            transaction: tr,
            symbol_table: st,
            stepid: step,
            args,
        }
    }

    pub fn next_step(&self, evaluator: &mut Evaluator) -> Option<StmtId> {
        // Sends step to next, then gets step and modifies
        evaluator.switch_args_mapping(self.args.clone());
        let res = evaluator
            .evaluate_until_step(&self.stepid)
            .unwrap_or_default();
        res
        // todo!("evaluate next step")
    }
}

pub struct Scheduler<'a> {
    active_threads: Vec<Thread<'a>>,
    next_threads: Vec<Thread<'a>>,
    inactive_threads: Vec<Thread<'a>>,
    step_count: i32,
    evaluator: Evaluator<'a>,
}

impl<'a> Scheduler<'a> {
    pub fn new(
        tr: &'a Transaction,
        st: &'a SymbolTable,
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

        // Initialize evaluator
        let evaluator = Evaluator::new(args.clone(), &tr, &st, handler, &ctx, &sys, sim);

        let first = Thread::initialize_thread(tr, st, step, args);
        Self {
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

            let next_step = next_thread.next_step(&mut self.evaluator);
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
}
