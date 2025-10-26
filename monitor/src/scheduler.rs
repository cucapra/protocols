// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use anyhow::anyhow;
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

/// Formats a queue's contents into a pretty-printed string
/// Note: we can't implement the `Display` trait for `Queue` since
/// `Queue` is just a type alias
fn format_queue(queue: &Queue) -> String {
    if !queue.is_empty() {
        let formatted_queue = queue
            .iter()
            .map(|thread| format!("{}", thread))
            .collect::<Vec<String>>()
            .join("\n\t");
        format!("\n\t{}", formatted_queue)
    } else {
        "<EMPTY>".to_string()
    }
}

/// Formats a queue's contents into a *compact* pretty-printed string
/// (i.e. no new-lines, only displays the thread_id and transaction name
/// for each thread)
fn format_queue_compact(queue: &Queue) -> String {
    if !queue.is_empty() {
        queue
            .iter()
            .map(|thread| {
                format!(
                    "Thread {} (`{}`)",
                    thread.thread_id, thread.transaction.name
                )
            })
            .collect::<Vec<_>>()
            .join(", ")
    } else {
        "<EMPTY>".to_string()
    }
}

/// Extracts all elements in the `Queue` where all the threads have the
/// same `start_cycle`, preserving their order
pub fn threads_with_start_time(queue: &Queue, start_cycle: u32) -> Queue {
    queue
        .clone()
        .into_iter()
        .filter(|thread| thread.start_cycle == start_cycle)
        .collect()
}

/// Finds all the unique start cycles of all the threads in the same queue
pub fn unique_start_cycles(queue: &Queue) -> HashSet<u32> {
    let start_cycles: Vec<u32> = queue.iter().map(|thread| thread.start_cycle).collect();
    HashSet::from_iter(start_cycles)
}

/// Scheduler for handling the multiple threads in the monitor
pub struct Scheduler {
    /// Queue storing threads that are ready (to be run during the current step)
    current: Queue,

    /// Queue of suspended threads (to be run during the next step)
    next: Queue,

    /// Threads that have finished successfully
    finished: Queue,

    /// Threads that failed
    failed: Queue,

    /// The global context (shared across all threads)
    ctx: GlobalContext,

    /// The current scheduling cycle
    cycle_count: u32,

    /// The no. of threads that have been created so far.
    /// (This variable is used to create unique `thread_id`s for `Thread`s.)
    num_threads: u32,

    /// The associated interpreter for Protocols programs
    interpreter: Interpreter,

    /// Flag indicating whether the trace has ended
    trace_ended: bool,

    /// All possible transactions (along with their corresponding transactions)
    /// (This is used when forking new threads)
    possible_transactions: Vec<(Transaction, SymbolTable)>,
}

impl Scheduler {
    /// Prints the internal state of the scheduler
    /// (i.e. the contents of all 4 queues + current scheduling cycle)
    pub fn print_scheduler_state(&self) {
        info!(
            "{}\n{}\n{}\n{}\n{}",
            format_args!("SCHULEDER STATE, CYCLE {}:", self.cycle_count),
            format_args!("Current: {}", format_queue(&self.current)),
            format_args!("Next: {}", format_queue(&self.next)),
            format_args!("Failed: {}", format_queue(&self.failed)),
            format_args!("Finished: {}", format_queue(&self.finished))
        );
    }

    /// Initializes a `Scheduler` with one scheduled thread for each `(Transcation, SymbolTable)`
    /// pair in the argument `transactions`, along with a `GlobalContext` that is
    /// shared across all threads
    pub fn initialize(transactions: Vec<(Transaction, SymbolTable)>, ctx: GlobalContext) -> Self {
        let cycle_count = 0;
        let mut thread_id = 0;
        let mut current_threads = vec![];
        // Create a new thread for each transaction, then push it to the
        // end of the `current` queue
        for (transaction, symbol_table) in &transactions {
            let args_mapping = HashMap::new();
            let thread = Thread::new(
                transaction.clone(),
                symbol_table.clone(),
                transaction.next_stmt_mapping(),
                args_mapping,
                &ctx,
                thread_id,
                cycle_count,
            );
            current_threads.push(thread);
            thread_id += 1;
        }
        // Technically, initializing the `interpreter` here is necessary
        // since when we pop a thread from the `current` queue, we perform
        // a context switch and run the `interpreter` on the transaction/symbol_table
        // corresponding to the thread. However, we do this here nonetheless
        // since we need to initialize all fields in `Scheduler` struct.
        let initial_thread = &current_threads[0];
        let initial_transaction = initial_thread.transaction.clone();
        let initial_symbol_table = initial_thread.symbol_table.clone();
        let interpreter =
            Interpreter::new(initial_transaction, initial_symbol_table, &ctx, cycle_count);
        Self {
            current: current_threads,
            next: vec![],
            finished: vec![],
            failed: vec![],
            ctx,
            interpreter,
            cycle_count,
            num_threads: thread_id,
            trace_ended: false,
            possible_transactions: transactions,
        }
    }

    /// Runs the scheduler by repeating the following steps.
    /// 1. Pops a thread from the `current` queue and runs it till the next step.
    ///    We keep doing this while the `current` queue is non-empty.
    /// 2. When the `current` queue is empty, it sets `current` to `next`
    ///    (marking all suspended threads as ready for execution),
    ///    then advances the trace to the next step.
    pub fn run(&mut self) -> anyhow::Result<()> {
        loop {
            self.print_scheduler_state();

            while let Some(thread) = self.current.pop() {
                self.run_thread_till_next_step(thread);
            }

            // At this point, all threads have been executed till their next `step`
            // and are synchronized (i.e. `current` is empty)

            // Find the unique start cycles of all threads in the `finished` queue
            let finished_threads_start_cycles = unique_start_cycles(&self.finished);

            // Out of all threads that started in the same cycle & finished in the most recent step...
            for start_cycle in finished_threads_start_cycles {
                // ...there should only be at most one of them in `finished`
                let finished = threads_with_start_time(&self.finished, start_cycle);
                if finished.len() > 1 {
                    return Err(anyhow!(
                        "Expected the no. of threads that started in cycle {} & ended in cycle {} to be at most 1, but instead there were {}",
                        start_cycle,
                        self.cycle_count,
                        finished.len()
                    ));
                }
                let finished_thread = &finished[0];

                // ...and there shouldn't be any other threads in `next`
                let next = threads_with_start_time(&self.next, start_cycle);
                if !next.is_empty() {
                    return Err(anyhow!(
                        "Thread {} finished but there are other threads with the same start cycle {} in the `next` queue",
                        finished_thread.thread_id,
                        finished_thread.start_cycle
                    ));
                }
            }

            // Next, find the unique start cycles of all threads in `failed`
            let failed_threads_start_cycles = unique_start_cycles(&self.failed);

            // Out of all threads that started in the same cycle & failed in the most recent step...
            for start_cycle in failed_threads_start_cycles {
                // ...if `failed` is non-empty, but `next` and `finished` are non-empty,
                // then we should emit an error
                // (The expected behavior is that all but one threads that started in
                // the same cycle should fail, but here we have the case where
                // *all* the threads that started in the same cycle failed)
                let failed = threads_with_start_time(&self.failed, start_cycle);
                let finished = threads_with_start_time(&self.finished, start_cycle);
                let paused = threads_with_start_time(&self.next, start_cycle);
                if !failed.is_empty() && finished.is_empty() && paused.is_empty() {
                    return Err(anyhow!(
                        "Out of all {} threads that started in {}, all but one are expected to fail, but all of them failed",
                        finished.len(),
                        start_cycle
                    ));
                }
            }

            // Print all the threads that finished & failed during the most recent step
            if !self.failed.is_empty() {
                info!(
                    "Threads that failed in cycle {}: {}",
                    self.cycle_count,
                    format_queue_compact(&self.failed)
                );
                self.failed.clear();
            }

            if !self.finished.is_empty() {
                info!(
                    "Threads that finished in cycle {}: {}",
                    self.cycle_count,
                    format_queue_compact(&self.finished)
                );
                self.finished.clear();
            }

            if !self.next.is_empty() {
                // If the trace has already ended, terminate the scheduler
                if self.trace_ended {
                    info!(
                        "Trace has ended, threads in `next` can't proceed, terminating scheduler w/ final state:"
                    );
                    self.print_scheduler_state();
                    break;
                }

                // Mark all suspended threads as ready for execution
                // by setting `current` to `next`, and setting `next = []`
                // (the latter is done via `std::mem::take`)
                self.current = std::mem::take(&mut self.next);

                // Then, advance the trace to the next `step` and update
                // the scheduler's `cycle_count` (along with the corresponding
                // `trace_cycle_count` in the interpreter)
                let step_result = self.ctx.trace.step();

                self.cycle_count += 1;
                self.interpreter.trace_cycle_count += 1;
                info!(
                    "Advancing to cycle {}, setting current = next",
                    self.cycle_count
                );

                if let StepResult::Done = step_result {
                    // If `StepResult = Done`, the trace has ended.
                    // Set `trace_ended = true` and continue
                    // executing threads in `current`
                    info!("No steps remaining left in signal trace");
                    self.trace_ended = true;
                }
            } else {
                // When both current and next are finished, the monitor is done
                // since there are no more threads to run
                info!("Monitor finished!");
                break;
            }
        }
        Ok(())
    }

    /// Keeps running a `thread` until:
    /// - It reaches the next `step()` or `fork()` statement
    /// - It completes succesfully
    /// - An error was encountered during execution
    pub fn run_thread_till_next_step(&mut self, mut thread: Thread) {
        info!(
            "Running thread {} (transaction `{}`) till next `step()`...",
            thread.thread_id, thread.transaction.name
        );

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
                                "Thread {:?} (transaction `{}`) called `step()`, moving to `next` queue",
                                thread.thread_id,
                                thread.transaction.clone().name,
                            );
                            // if the thread is moving to the `next` queue,
                            // its `current_stmt_id` is updated to be `next_stmt_id`
                            thread.current_stmt_id = next_stmt_id;
                            self.next.push(thread);
                            self.print_scheduler_state();
                            break;
                        }
                        Stmt::Fork => {
                            // For each possible transaction, fork one new thread for it,
                            // i.e. add it to the `current` queue
                            // This means if there are `n` possible transactions,
                            // we push `n` threads to the `current` queue.
                            info!(
                                "Thread {:?} called `fork()`, creating new threads...",
                                thread.thread_id
                            );
                            for (transaction, symbol_table) in &self.possible_transactions {
                                let new_thread = Thread::new(
                                    transaction.clone(),
                                    symbol_table.clone(),
                                    thread.next_stmt_map.clone(),
                                    thread.args_mapping.clone(),
                                    &self.ctx,
                                    self.num_threads,
                                    self.cycle_count,
                                );
                                self.num_threads += 1;
                                info!(
                                    "Adding new thread {:?} (`{}`) to `current` queue",
                                    new_thread.thread_id, new_thread.transaction.name
                                );
                                self.current.push(new_thread);
                            }

                            self.print_scheduler_state();

                            // Continue from the fork statement onwards
                            current_stmt_id = next_stmt_id;
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
                        "Thread {:?} finished successfully, adding to `finished` queue",
                        thread.thread_id
                    );
                    println!(
                        "{}",
                        self.interpreter
                            .serialize_reconstructed_transaction(&self.ctx)
                    );
                    self.finished.push(thread.clone());
                    break;
                }
                Err(e) => {
                    info!(
                        "Thread {:?} encountered error {}, adding to `failed` queue",
                        thread.thread_id, e
                    );
                    self.failed.push(thread);
                    self.print_scheduler_state();
                    break;
                }
            }
        }
    }
}
