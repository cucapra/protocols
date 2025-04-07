// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use std::collections::HashMap;

use crate::ir::*;

#[derive(Debug, Clone)]
pub struct Thread {
    pub transaction: Transaction,
    pub stepid: StmtId,
    args: HashMap<Arg, BitVecValue>,
}

impl Thread {
    pub fn initialize_thread(
        tr: Transaction,
        step: StmtId,
        args: HashMap<Arg, BitVecValue>,
    ) -> Self {
        Self {
            transaction: tr,
            stepid: step,
            args,
        }
    }

    pub fn next_step(&self) -> Option<StmtId> {
        // Sends step to next, then gets step and modifies
        todo!("evaluate next step")
    }
}

pub struct Scheduler {
    active_threads: Vec<Thread>,
    next_threads: Vec<Thread>,
    inactive_threads: Vec<Thread>,
    step_count: i32,
}

impl Scheduler {
    pub fn new(tr: Transaction, step: StmtId, args: HashMap<Arg, BitVecValue>) -> Self {
        let first = Thread::initialize_thread(tr, step, args);
        Self {
            active_threads: vec![first],
            next_threads: vec![],
            inactive_threads: vec![],
            step_count: 1,
        }
    }

    pub fn add_thread(&mut self, tr: Transaction, step: StmtId, args: HashMap<Arg, BitVecValue>) {
        let new_thread = Thread::initialize_thread(tr, step, args);
        self.next_threads.push(new_thread);
    }

    pub fn schedule_threads(&mut self) {
        while self.active_threads.len() > 0 {
            let mut next_thread = self.active_threads.pop().unwrap();

            let next_step = next_thread.next_step();
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
