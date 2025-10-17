// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use log::info;
use protocols::ir::{Stmt, SymbolTable, Transaction};

use crate::{
    global_context::GlobalContext,
    interpreter::Interpreter,
    signal_trace::{SignalTrace, StepResult},
    thread::Thread,
};

/// `Queue` is just a type alias for `Vec<Thread>`
type Queue = Vec<Thread>;

/// Extracts all elements in the `Queue` where all the threads have the
/// same `start_cycle`, preserving their order
pub fn threads_with_start_time(queue: Queue, start_cycle: u32) -> Queue {
    queue
        .into_iter()
        .filter(|thread| thread.start_cycle == start_cycle)
        .collect()
}

/// Scheduler for handling the multiple threads in the monitor
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

    /// Runs the scheduler by repeating the following steps.
    /// 1. Pops a thread from the `current` queue and runs it till the next step.
    ///    We keep doing this while the `current` queue is non-empty.
    /// 2. When the `current` queue is empty, it sets `current` to `next`
    ///    (marking all suspended threads as ready for execution),
    ///    then advances the trace to the next step.
    pub fn run(&mut self) {
        loop {
            while let Some(thread) = self.current.pop() {
                self.run_thread_till_next_step(thread);
            }
            // At this point, `current` is empty
            // (i.e. all threads have been executed till their next `step`)
            if !self.next.is_empty() {
                // Mark all suspended threads as ready for execution
                // by setting `current` to `next`, and setting `next = []`
                // (the latter is done via `std::mem::take`)
                self.current = std::mem::take(&mut self.next);

                // Then, advance the trace to the next `step`
                let step_result = self.ctx.trace.step();
                // `trace.step()` returns a `StepResult` which is
                // either `Done` or `Ok`.
                // If `StepResult = Done`, there are no more steps
                // left in the signal trace
                if let StepResult::Done = step_result {
                    // The trace has ended, so we can just return here
                    info!("No steps remaining left in signal trace");
                    break;
                }
            } else {
                // When both current and next are finished, the monitor is done
                // since there are no more threads to run
                info!("Monitor finished!");
                break;
            }
        }
    }

    /// Runs a `thread` until:
    /// - It reaches the next `step()` or `fork()` statement
    /// - It completes succesfully
    /// - An error was encountered during execution
    pub fn run_thread_till_next_step(&mut self, mut thread: Thread) {
        // Perform a context switch (use the argument thread's `Transaction`
        // & associated `SymbolTable` / `NextStmtMap`)
        let Thread {
            transaction,
            symbol_table,
            next_stmt_map,
            args_mapping,
            ..
        } = thread.clone();
        self.interpreter
            .context_switch(transaction, symbol_table, next_stmt_map, args_mapping);
        let mut current_stmt_id = thread.current_stmt_id;

        loop {
            match self.interpreter.evaluate_stmt(&current_stmt_id, &self.ctx) {
                Ok(Some(next_stmt_id)) => {
                    // Update the thread-local `args_mapping` to be the resultant
                    // arg map in the interpreter
                    thread.args_mapping = self.interpreter.args_mapping.clone();

                    // Check whether the next statement is `Step` or `Fork`
                    // This determines if we need to move threads to/from different queues
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
                                thread.next_stmt_map,
                                thread.args_mapping,
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
                    println!(
                        "Reconstructed transaction: {}",
                        self.interpreter
                            .serialize_reconstructed_transaction(&self.ctx)
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
