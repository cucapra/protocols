// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use log::info;
use protocols::ir::{Stmt, SymbolTable, Transaction};

use crate::{global_context::GlobalContext, interpreter::Interpreter, thread::Thread};

/// Queue of threads
type Queue = Vec<Thread>;

/// Extracts all elements in the `Queue` where all the threads have the
/// same `start_cycle`, preserving their order
pub fn threads_with_start_time(queue: Queue, start_cycle: u32) -> Queue {
    queue
        .into_iter()
        .filter(|thread| thread.start_cycle == start_cycle)
        .collect()
}

pub struct Scheduler {
    /// Queue storing threads that are ready (to be run during the current step)
    current: Queue,

    /// Queue of suspended threads (to be run during the next step)
    next: Queue,

    /// Threads that have completed successfully
    completed: Queue,

    /// Threads that failed
    failed: Queue,

    /// The global context (shared across all threads)
    ctx: GlobalContext,

    /// The current scheduling cycle
    step_count: u32,

    /// The no. of threads that have been created so far.  
    /// (This variable is used to create unique `thread_id`s for `Thread`s.)
    num_threads: u32,

    /// The associated interpreter for Protocols programs
    interpreter: Interpreter,
}

impl Scheduler {
    /// Creates a new `Scheduler` where all four queues are empty
    pub fn new(transaction: Transaction, symbol_table: SymbolTable, ctx: GlobalContext) -> Self {
        let interpreter = Interpreter::new(transaction, symbol_table, &ctx);
        Self {
            current: vec![],
            next: vec![],
            completed: vec![],
            failed: vec![],
            ctx,
            interpreter,
            step_count: 0,
            num_threads: 0,
        }
    }

    pub fn run_scheduler(&mut self) {
        if let Some(thread) = self.current.pop() {
            self.run_thread_till_next_step(thread);
        } else if !self.next.is_empty() {
            todo!("Swap current and next");
        } else {
            todo!("Figure out what to do when both current and next are empty");
        }
    }

    /// Pops a thread from the `current` queue and runs it till the next `step()` or `fork()` statement
    pub fn run_thread_till_next_step(&mut self, mut thread: Thread) {
        let mut current_stmt_id = thread.current_stmt_id;

        loop {
            match self.interpreter.evaluate_stmt(&current_stmt_id, &self.ctx) {
                Ok(Some(next_stmt_id)) => {
                    match thread.transaction[next_stmt_id] {
                        Stmt::Step => {
                            info!(
                                "Thread {:?} called `step()`, adding to `next` queue",
                                thread.thread_id
                            );
                            // if the thread is moving to the `next` queue,
                            // its `current_stmt_id` is updated to be `next_stmt_id`
                            thread.current_stmt_id = next_stmt_id;
                            self.next.push(thread);
                            break;
                        }
                        Stmt::Fork => {
                            let new_thread = Thread::new(
                                thread.transaction,
                                thread.symbol_table,
                                &self.ctx,
                                self.num_threads,
                                self.step_count,
                            );
                            self.num_threads += 1;
                            info!(
                                "Thread {:?} called `fork(), created new thread {:?} for transaction {}, adding to `current` queue",
                                thread.thread_id, new_thread.thread_id, new_thread.transaction.name
                            );
                            self.current.push(new_thread);
                            break;
                        }
                        _ => {
                            // Default case: update `current_stmt_id`
                            // to point to `next_stmt_id`
                            current_stmt_id = next_stmt_id;
                        }
                    }
                }
                Ok(None) => {
                    info!(
                        "Thread {:?} completed successfully, adding to `completed` queue",
                        thread.thread_id
                    );
                    self.completed.push(thread);
                    break;
                }
                Err(e) => {
                    info!(
                        "Thread {:?} encountered error {}, adding to `failed` queue",
                        thread.thread_id, e
                    );
                    self.failed.push(thread);
                    break;
                }
            }
        }
    }
}
