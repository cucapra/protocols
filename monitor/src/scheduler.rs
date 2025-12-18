// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use anyhow::{anyhow, Context};
use baa::BitVecOps;
use log::info;
use protocols::{
    errors::{EvaluationError, ExecutionError},
    ir::{Stmt, SymbolTable, Transaction},
    serialize::{serialize_bitvec, serialize_stmt},
};

use crate::{
    global_context::GlobalContext,
    interpreter::Interpreter,
    signal_trace::{SignalTrace, StepResult, WaveSignalTrace},
    thread::Thread,
};

/// `Queue` is just a type alias for `Vec<Thread>`
type Queue = Vec<Thread>;

/// Formats a queue's contents into a pretty-printed string
/// Note: we can't implement the `Display` trait for `Queue` since
/// `Queue` is just a type alias
fn format_queue(queue: &Queue, ctx: &GlobalContext, trace: &WaveSignalTrace) -> String {
    if !queue.is_empty() {
        let formatted_queue = queue
            .iter()
            .map(|thread| format_thread(thread, ctx, trace))
            .collect::<Vec<String>>()
            .join("\n\t");
        format!("\n\t{}", formatted_queue)
    } else {
        "<EMPTY>".to_string()
    }
}

/// Formats a single thread with context-aware timing information
fn format_thread(thread: &Thread, ctx: &GlobalContext, trace: &WaveSignalTrace) -> String {
    let start_info = if ctx.show_waveform_time {
        format!(
            "Start time: {}",
            trace.format_time(thread.start_time_step, ctx.time_unit)
        )
    } else {
        format!("Start cycle: {}", thread.start_cycle)
    };

    format!(
        "THREAD {}: {{ {}, Transaction: `{}`, Current stmt: `{}` ({}) }}",
        thread.thread_id,
        start_info,
        thread.transaction.name,
        serialize_stmt(
            &thread.transaction,
            &thread.symbol_table,
            &thread.current_stmt_id
        ),
        thread.current_stmt_id
    )
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
pub fn unique_start_cycles(queue: &Queue) -> Vec<u32> {
    let mut start_cycles: Vec<u32> = queue.iter().map(|thread| thread.start_cycle).collect();
    start_cycles.sort();
    start_cycles.dedup();
    start_cycles
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

    /// All possible transactions (along with their corresponding `SymbolTable`s)
    /// (This is used when forking new threads)
    possible_transactions: Vec<(Transaction, SymbolTable)>,

    /// The name of the struct this scheduler is monitoring
    /// (Used for prefixing transaction names in multi-struct scenarios)
    /// Note: if there is just one single struct, this string is empty
    struct_name: String,
}

impl Scheduler {
    /// Prints the internal state of the scheduler
    /// (i.e. the contents of all 4 queues + current scheduling cycle)
    pub fn print_scheduler_state(&self, trace: &WaveSignalTrace) {
        let time_step = trace.time_step();
        let header = if self.ctx.show_waveform_time {
            format!(
                "SCHEDULER STATE, TIME {}:",
                trace.format_time(time_step, self.ctx.time_unit)
            )
        } else {
            format!("SCHEDULER STATE, CYCLE {}:", self.cycle_count)
        };
        info!(
            "{}\n{}\n{}\n{}\n{}",
            header,
            format_args!("Current: {}", format_queue(&self.current, &self.ctx, trace)),
            format_args!("Next: {}", format_queue(&self.next, &self.ctx, trace)),
            format_args!("Failed: {}", format_queue(&self.failed, &self.ctx, trace)),
            format_args!(
                "Finished: {}",
                format_queue(&self.finished, &self.ctx, trace)
            )
        );
    }

    /// Initializes a `Scheduler` with one scheduled thread for each `(Transcation, SymbolTable)`
    /// pair in the argument `transactions`, along with a `GlobalContext` that is
    /// shared across all threads
    pub fn initialize(
        transactions: Vec<(Transaction, SymbolTable)>,
        ctx: GlobalContext,
        trace: &WaveSignalTrace,
        struct_name: String,
    ) -> Self {
        let cycle_count = 0;
        let mut thread_id = 0;
        let mut current_threads = vec![];
        // Create a new thread for each transaction, then push it to the
        // end of the `current` queue
        for (transaction, symbol_table) in &transactions {
            let thread = Thread::new(
                transaction.clone(),
                symbol_table.clone(),
                transaction.next_stmt_mapping(),
                &ctx,
                trace,
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
        let interpreter = Interpreter::new(
            initial_transaction,
            initial_symbol_table,
            &ctx,
            trace,
            cycle_count,
        );
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
            struct_name,
        }
    }

    /// Runs the current phase: executes all threads in the `current` queue
    /// and checks constraints for threads in the `next` queue.
    /// This function is used by `GlobalScheduler` to coordinate execution
    /// between multiple schedulers
    pub fn run_current_phase(&mut self, trace: &WaveSignalTrace) -> anyhow::Result<()> {
        self.print_scheduler_state(trace);

        // Run all threads in the current queue
        while let Some(thread) = self.current.pop() {
            self.run_thread_till_next_step(thread, trace);
        }

        // Check constraints for all threads in the `next` queue
        let mut failed_constraint_checks = vec![];

        for thread in self.next.iter_mut() {
            let time_str = if self.ctx.show_waveform_time {
                trace.format_time(trace.time_step(), self.ctx.time_unit)
            } else {
                format!("cycle {}", self.interpreter.trace_cycle_count)
            };

            // Check constraints
            for (symbol_id, expected_value) in &thread.constraints {
                let symbol_name = thread.symbol_table.full_name_from_symbol_id(symbol_id);

                match trace.get(self.ctx.instance_id, *symbol_id) {
                    Ok(trace_value) => {
                        if trace_value != *expected_value {
                            let formatted_transaction = if !self.struct_name.is_empty() {
                                format!("{}::{}", self.struct_name, thread.transaction.name)
                            } else {
                                thread.transaction.name.clone()
                            };

                            info!(
                                "Constraint FAILED for thread {} (`{}`) at {}: {} = {} (trace) != {} (expected)",
                                thread.thread_id,
                                formatted_transaction,
                                time_str,
                                symbol_name,
                                serialize_bitvec(&trace_value, self.ctx.display_hex),
                                serialize_bitvec(expected_value, self.ctx.display_hex)
                            );
                            failed_constraint_checks.push(thread.clone());
                        }
                    }
                    Err(err) => {
                        failed_constraint_checks.push(thread.clone());
                        return Err(anyhow!(
                            "Failed to get value for {} from trace: {}",
                            symbol_name,
                            err
                        ));
                    }
                }
            }

            // Update args_mapping based on waveform data
            for (param_id, port_id) in &thread.args_to_pins {
                let param_name = thread.symbol_table.full_name_from_symbol_id(param_id);
                let port_name = thread.symbol_table.full_name_from_symbol_id(port_id);

                if let Some(param_value) = thread.args_mapping.get(param_id) {
                    let time_str = if self.ctx.show_waveform_time {
                        trace.format_time(trace.time_step(), self.ctx.time_unit)
                    } else {
                        format!("cycle {}", self.interpreter.trace_cycle_count)
                    };

                    match trace.get(self.ctx.instance_id, *port_id) {
                        Ok(trace_value) => {
                            let known_bits = thread.known_bits.get(param_id).ok_or_else(|| {
                                anyhow!(
                                    "Unable to find {} in `known_bits` map of thread {} ({})",
                                    param_name,
                                    thread.thread_id,
                                    thread.transaction.name
                                )
                            })?;
                            let all_bits_known = known_bits.is_all_ones();

                            if all_bits_known && trace_value.width() == param_value.width() {
                                if trace_value != *param_value {
                                    info!(
                                        "Updating {} |-> {} in args_mapping based on waveform data at {}",
                                        param_name,
                                        serialize_bitvec(&trace_value, self.ctx.display_hex),
                                        time_str
                                    );
                                    thread.args_mapping.insert(*param_id, trace_value);
                                } else {
                                    info!(
                                        "args_mapping OK: {} = {} = {}",
                                        param_name,
                                        port_name,
                                        serialize_bitvec(param_value, self.ctx.display_hex)
                                    );
                                }
                            }
                        }
                        Err(err) => {
                            return Err(anyhow!(
                                "Failed to get value for {} from trace: {}",
                                port_name,
                                err
                            ));
                        }
                    }
                }
            }
        }

        // Move failed threads to the failed queue
        for failed_thread in &failed_constraint_checks {
            self.next.retain(|t| t.thread_id != failed_thread.thread_id);
            self.failed.push(failed_thread.clone());
        }

        // Check that threads in the `finished` and `failed` queues
        // behave as expected
        self.validate_finished_and_failed_threads(trace)?;

        Ok(())
    }

    /// Validates that threads in the `finished` and `failed` queues
    /// behave as expected
    fn validate_finished_and_failed_threads(
        &mut self,
        trace: &WaveSignalTrace,
    ) -> anyhow::Result<()> {
        // Clear finished threads and print if needed
        if !self.finished.is_empty() {
            if self.ctx.print_num_steps {
                info!("Finished: {}", format_queue_compact(&self.finished));
            }
            self.finished.clear();
        }

        // Check finished threads follow expected patterns
        let finished_threads_start_cycles = unique_start_cycles(&self.finished);
        for start_cycle in finished_threads_start_cycles {
            let finished = threads_with_start_time(&self.finished, start_cycle);
            if finished.len() > 1 {
                let start_time = if self.ctx.show_waveform_time {
                    trace.format_time(finished[0].start_time_step, self.ctx.time_unit)
                } else {
                    format!("cycle {}", self.cycle_count)
                };

                self.print_step_count();
                return Err(anyhow!(
                    "Expected at most 1 thread to finish at {}, but {} finished: {:?}",
                    start_time,
                    finished.len(),
                    finished
                        .iter()
                        .map(|t| t.transaction.name.clone())
                        .collect::<Vec<_>>()
                ));
            }
        }

        // Check failed threads
        let failed_threads_start_cycles = unique_start_cycles(&self.failed);
        for start_cycle in failed_threads_start_cycles {
            let failed = threads_with_start_time(&self.failed, start_cycle);
            let finished = threads_with_start_time(&self.finished, start_cycle);
            let next = threads_with_start_time(&self.next, start_cycle);

            if !failed.is_empty() && finished.is_empty() && next.is_empty() {
                return self.emit_error(trace).with_context(|| {
                    anyhow!(
                        "All {} threads that started in cycle {} failed",
                        failed.len(),
                        start_cycle
                    )
                });
            }
        }

        Ok(())
    }

    /// Runs the scheduler by repeating the following steps.
    /// 1. Pops a thread from the `current` queue and runs it till the next step.
    ///    We keep doing this while the `current` queue is non-empty.
    /// 2. When the `current` queue is empty, it sets `current` to `next`
    ///    (marking all suspended threads as ready for execution),
    ///    then advances the trace to the next step.
    pub fn run(&mut self, trace: &mut WaveSignalTrace) -> anyhow::Result<()> {
        loop {
            self.print_scheduler_state(trace);

            while let Some(thread) = self.current.pop() {
                self.run_thread_till_next_step(thread, trace);
            }

            // At this point, all threads have been executed till their next `step`
            // and are synchronized (i.e. `current` is empty)

            // Check constraints for all threads in the `next` queue.
            // These threads have called `step()` and have more work to do.
            // Threads that finished (i.e. they executed the `step()` statement at t
            // the end of a function) are not in `next`, so they won't be checked.
            let mut failed_constraint_checks = Vec::new();

            for thread in self.next.iter_mut() {
                // If any constraints failed, figure out the right time-step/cycle
                // to display in the logs
                let time_str = if self.ctx.show_waveform_time {
                    trace.format_time(trace.time_step(), self.ctx.time_unit)
                } else {
                    format!("cycle {}", self.interpreter.trace_cycle_count)
                };

                // Check that all constraints in the `constraints` map still hold
                // against the current trace values. This is called after each `step()`
                // to ensure that assignments like `D.m_axis_tvalid := 1'b1` continue
                // to hold after stepping to a new cycle.
                for (symbol_id, expected_value) in &thread.constraints {
                    let symbol_name = thread.symbol_table.full_name_from_symbol_id(symbol_id);

                    match trace.get(self.ctx.instance_id, *symbol_id) {
                        Ok(trace_value) => {
                            if trace_value != *expected_value {
                                info!(
                                    "Constraint FAILED for thread {} (`{}`) at {}: {} = {} (trace) != {} (expected)",
                                    thread.thread_id,
                                    thread.transaction.name,
                                    time_str,
                                    symbol_name,
                                    serialize_bitvec(&trace_value, self.ctx.display_hex),
                                    serialize_bitvec(expected_value, self.ctx.display_hex)
                                );
                                failed_constraint_checks.push(thread.clone());
                            } else {
                                info!(
                                    "Constraint OK for thread {} (`{}`) at {}: {} = {}",
                                    thread.thread_id,
                                    thread.transaction.name,
                                    time_str,
                                    symbol_name,
                                    serialize_bitvec(expected_value, self.ctx.display_hex)
                                );
                            }
                        }
                        Err(_) => {
                            info!(
                                "Unable to verify constraint for {} at cycle {:?} - symbol not found in trace",
                                symbol_name, self.interpreter.trace_cycle_count
                            );
                            // If we can't read the symbol from the trace, treat it as a constraint violation
                            // (The constraint can't hold if the signal doesn't exist in the trace)
                            failed_constraint_checks.push(thread.clone());
                        }
                    }
                }

                // Check that all args_mappings in the `args_to_pins` map still hold
                // against the current trace values. This is called after each `step()`
                // to ensure that parameters inferred from DUT ports (like `data` from `D.m_axis_tdata`)
                // still match the trace after stepping to a new cycle.
                for (param_id, port_id) in &thread.args_to_pins {
                    let param_name = thread.symbol_table.full_name_from_symbol_id(param_id);
                    let port_name = thread.symbol_table.full_name_from_symbol_id(port_id);

                    // Get the (existing) inferred parameter value from args_mapping
                    if let Some(param_value) = thread.args_mapping.get(param_id) {
                        // Compute the current time-step/cycle (for logging purposes)
                        let time_str = if self.ctx.show_waveform_time {
                            trace.format_time(trace.time_step(), self.ctx.time_unit)
                        } else {
                            format!("cycle {}", self.interpreter.trace_cycle_count)
                        };

                        // Get the current port value from the trace
                        match trace.get(self.ctx.instance_id, *port_id) {
                            Ok(trace_value) => {
                                // Check whether all bits are known or if only
                                // some of them are known (e.g. due to a bit-slice)
                                let known_bits =
                                    thread.known_bits.get(param_id).ok_or_else(|| {
                                        anyhow!(
                                            "Unable to find {} in `known_bits` map of thread {} ({})",
                                            param_name,
                                            thread.thread_id,
                                            thread.transaction.name
                                        )}).context(format!("known_bits = {:?}", thread.known_bits))?;
                                let all_bits_known = known_bits.is_all_ones();

                                // TODO: need to handle the case when not all bits are known

                                // If all bits are known and the two sides of the assignment have the
                                // same bit-width, check whether the inferred values for function parameters
                                // abide by the waveform data.
                                // (We add the bit-width check for simplicity so we don't have
                                // to handle re-assignments to the same port that involve bit-slices for now,
                                // as is the case for the SERV example.)
                                if all_bits_known && trace_value.width() == param_value.width() {
                                    // If there are any discrepancies between the existing
                                    // inferred value for a function parameter and its
                                    // waveform value, we update the inferred value to be
                                    // the waveform value at the current time-step.
                                    if trace_value != *param_value {
                                        info!(
                                            "Updating {} |-> {} in args_mapping based on waveform data at {}",
                                            param_name,
                                            serialize_bitvec(&trace_value, self.ctx.display_hex),
                                            time_str
                                        );
                                        thread.args_mapping.insert(*param_id, trace_value);
                                    } else {
                                        info!(
                                            "args_mapping OK: {} = {} = {}",
                                            param_name,
                                            port_name,
                                            serialize_bitvec(param_value, self.ctx.display_hex)
                                        );
                                    }
                                } else {
                                    info!(
                                        "Skipping args_mapping check for {} since not all bits are known",
                                        param_name
                                    );
                                }
                            }
                            Err(_) => {
                                info!(
                                    "Unable to verify args_mapping {} -> {} at {}, as {} is not found in the trace",
                                    param_name, port_name, time_str, param_name
                                );
                                failed_constraint_checks.push(thread.clone());
                            }
                        }
                    }
                }
            }

            // Remove threads that failed constraint checks from `next` and add to `failed`
            for failed_thread in failed_constraint_checks {
                info!(
                    "Moving thread {} (`{}`) to `failed` as it failed a constraint check",
                    failed_thread.thread_id, failed_thread.transaction.name
                );
                self.next.retain(|t| t.thread_id != failed_thread.thread_id);
                self.failed.push(failed_thread);
            }

            // Find the unique start cycles of all threads in the `finished` queue
            let finished_threads_start_cycles = unique_start_cycles(&self.finished);

            // Out of all threads that started in the same cycle & finished in the most recent step...
            for start_cycle in finished_threads_start_cycles {
                // ...there should only be at most one of them in `finished`
                let finished = threads_with_start_time(&self.finished, start_cycle);
                if finished.len() > 1 {
                    let start_time = if self.ctx.show_waveform_time {
                        trace.format_time(finished[0].start_time_step, self.ctx.time_unit)
                    } else {
                        format!("cycle {}", start_cycle)
                    };
                    let end_time = if self.ctx.show_waveform_time {
                        trace.format_time(
                            finished[0].end_time_step.unwrap_or_else(|| {
                                panic!(
                                    "Thread {} (`{}`) missing end_time_step",
                                    finished[0].thread_id, finished[0].transaction.name
                                )
                            }),
                            self.ctx.time_unit,
                        )
                    } else {
                        format!("cycle {}", self.cycle_count)
                    };

                    self.print_step_count();
                    return Err(anyhow!(
                        "Expected the no. of threads that started at {} & ended at {} to be at most 1, but instead there were {} ({:?})",
                        start_time,
                        end_time,
                        finished.len(),
                        finished
                            .iter()
                            .map(|t| t.transaction.name.clone())
                            .collect::<Vec<_>>()
                    ));
                }
                let finished_thread = &finished[0];

                // ...and there shouldn't be any other threads in `next`
                let next = threads_with_start_time(&self.next, start_cycle);
                if !next.is_empty() {
                    let start_time_str = if self.ctx.show_waveform_time {
                        trace.format_time(finished_thread.start_time_step, self.ctx.time_unit)
                    } else {
                        format!("cycle {}", finished_thread.start_cycle)
                    };
                    return self.emit_error(trace).with_context(|| anyhow!(
                            "Thread {} (`{}`) finished but there are other threads with the same start time ({}) in the `next` queue, namely {:?}",
                            finished_thread.thread_id,
                            finished_thread.transaction.name,
                            start_time_str,
                            next.iter().map(|t| t.transaction.name.clone()).collect::<Vec<_>>()
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

                // We also need to check whether the `next` queue contains
                // any threads (regardless of their start time) before emitting
                // an error. The reason is for protocols that currently end in
                // `step(); fork(); step()` (to comply with the well-formedness
                // constraints), there can be an edge case where a thread `t`
                // that started in an EARLIER cycle has been paused
                // (i.e. `t` is in `next`), but all
                // other threads started at the CURRENT `start_cycle` have failed.
                // In this case, we still need to try to run `t` since it may
                // succeed, even though all threads from the current cycle failed.
                // (Example: `picorv32/unsigned_mul.prot`)
                if failed.len() > 1
                    && finished.is_empty()
                    && paused.is_empty()
                    && self.next.is_empty()
                {
                    return self.emit_error(trace).with_context(|| anyhow!(
                        "Out of all threads that started in cycle {}, all but one are expected to fail, but all {} of them failed",
                        start_cycle,
                        failed.len()
                    ));
                }
            }

            // Print all the threads that finished & failed during the most recent step
            if !self.failed.is_empty() {
                if self.ctx.show_waveform_time {
                    let time_str = trace.format_time(trace.time_step(), self.ctx.time_unit);
                    info!(
                        "Threads that failed at time {}: {}",
                        time_str,
                        format_queue_compact(&self.failed)
                    );
                } else {
                    info!(
                        "Threads that failed in cycle {}: {}",
                        self.cycle_count,
                        format_queue_compact(&self.failed)
                    );
                }

                // If there are a non-zero no. of failed threads,
                // and there are no threads that finished succesfully /
                // no threads waiting to be run / no threads that are currently still running,
                // then we know that *all* threads have failed. In which case, we emit
                // an error message indicating that no transactions match the given waveform.
                let no_transactions_match =
                    self.current.is_empty() && self.next.is_empty() && self.finished.is_empty();

                if no_transactions_match {
                    return self.emit_error(trace);
                } else {
                    self.failed.clear();
                }
            }

            if !self.finished.is_empty() {
                if self.ctx.show_waveform_time {
                    let time_str = trace.format_time(trace.time_step(), self.ctx.time_unit);
                    info!(
                        "Threads that finished at time {}: {}",
                        time_str,
                        format_queue_compact(&self.finished)
                    );
                } else {
                    info!(
                        "Threads that finished in cycle {}: {}",
                        self.cycle_count,
                        format_queue_compact(&self.finished)
                    );
                }
                self.finished.clear();
            }

            if !self.next.is_empty() {
                // If the trace has already ended, terminate the scheduler
                if self.trace_ended {
                    info!(
                        "Trace has ended, threads in `next` can't proceed, terminating scheduler w/ final state:"
                    );
                    self.print_scheduler_state(trace);
                    break;
                }

                // Mark all suspended threads as ready for execution
                // by setting `current` to `next`, and setting `next = []`
                // (the latter is done via `std::mem::take`)
                self.current = std::mem::take(&mut self.next);

                // First, advance the trace to the next `step` and update
                // the scheduler's `cycle_count` (along with the corresponding
                // `trace_cycle_count` in the interpreter)
                let step_result = trace.step();

                self.cycle_count += 1;
                self.interpreter.trace_cycle_count += 1;
                if self.ctx.show_waveform_time {
                    let time_str = trace.format_time(trace.time_step(), self.ctx.time_unit);
                    info!("Advancing to time {}, setting current = next", time_str);
                } else {
                    info!(
                        "Advancing to cycle {}, setting current = next",
                        self.cycle_count
                    );
                }

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

        // Print the no. of logical steps (clock cycles) taken
        // by the monitor if the corresponding CLI flag has been set
        self.print_step_count();

        Ok(())
    }

    /// Helper function to print the number of steps taken
    fn print_step_count(&self) {
        if self.ctx.print_num_steps {
            eprintln!("No. of steps taken: {}", self.cycle_count);
        }
    }

    /// Returns true if the scheduler is completely done,
    /// i.e. both the `current` and `next` queues are empty
    pub fn is_done(&self) -> bool {
        self.current.is_empty() && self.next.is_empty()
    }

    /// Returns true if the scheduler needs to advance to the next time step
    /// (i.e. `current` is empty but `next` still contains threads,
    /// i.e. there are threads whose execution has been suspended
    /// and still need to be run to completion)
    pub fn needs_step(&self) -> bool {
        self.current.is_empty() && !self.next.is_empty()
    }

    /// Advances to the next cycle by moving next queue to current and incrementing cycle count
    /// (This function should only be called after `trace.step()` has been called)
    pub fn advance_to_next_cycle(&mut self) {
        // Note that `std::mem::take` also clears the `next` queue
        // behind the scenes
        self.current = std::mem::take(&mut self.next);
        self.cycle_count += 1;
        self.interpreter.trace_cycle_count += 1;
    }

    /// Marks the trace as having ended
    /// (This function is used by the `GlobalScheduler` when we reach
    /// the end of the trace)
    pub fn mark_trace_ended(&mut self) {
        self.trace_ended = true;
    }

    /// Helper function that emits an error (and terminates the monitor with
    /// non-zero exit code). The caller should only call this function
    /// when it is determined that no transactions match the provided waveform.
    pub fn emit_error(&self, trace: &WaveSignalTrace) -> anyhow::Result<()> {
        self.print_step_count();
        let time_str = if self.ctx.show_waveform_time {
            trace.format_time(trace.time_step(), self.ctx.time_unit)
        } else {
            format!("cycle {}", self.interpreter.trace_cycle_count)
        };

        let error_msg = anyhow!(
            "Failure at {}: No transactions match the waveform in `{}`.\nPossible transactions: [{}]",
            time_str,
            self.ctx.waveform_file,
            self.possible_transactions
                .iter()
                .map(|(tr, _)| tr.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        );
        Err(error_msg)
    }

    /// Keeps running a `thread` until:
    /// - It reaches the next `step()` or `fork()` statement
    /// - It completes succesfully
    /// - An error was encountered during execution
    pub fn run_thread_till_next_step(&mut self, mut thread: Thread, trace: &WaveSignalTrace) {
        info!(
            "Running thread {} (transaction `{}`) till next `step()`...",
            thread.thread_id, thread.transaction.name
        );

        // Perform a context switch (use the argument thread's `Transaction`
        // & associated `SymbolTable` / `NextStmtMap`)
        self.interpreter.context_switch(&thread);

        let mut current_stmt_id = thread.current_stmt_id;

        loop {
            match self
                .interpreter
                .evaluate_stmt(&current_stmt_id, &self.ctx, trace)
            {
                Ok(Some(next_stmt_id)) => {
                    // Update thread-local maps
                    // to be the resultant maps in the interpreter
                    thread.args_mapping = self.interpreter.args_mapping.clone();
                    thread.known_bits = self.interpreter.known_bits.clone();
                    thread.constraints = self.interpreter.constraints.clone();
                    thread.args_to_pins = self.interpreter.args_to_pins.clone();

                    // Check whether the next statement is `Step` or `Fork`
                    // This determines if we need to move threads to/from different queues
                    match thread.transaction[next_stmt_id] {
                        Stmt::Step => {
                            info!(
                                "Thread {:?} (transaction `{}`) called `step()`, moving to `next` queue",
                                thread.thread_id,
                                thread.transaction.clone().name,
                            );

                            // Update the thread's `end_time_step` field
                            // If this `step()` in the program is the very last
                            // statement in a function, then this field captures
                            // the end-time of the transaction
                            thread.end_time_step = Some(trace.time_step());

                            // if the thread is moving to the `next` queue,
                            // its `current_stmt_id` is updated to be `next_stmt_id`
                            thread.current_stmt_id = next_stmt_id;
                            self.next.push(thread);
                            self.print_scheduler_state(trace);
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
                                // Note: we use the new transaction's
                                // `next_stmt_mapping` when creating a new thread
                                let new_thread = Thread::new(
                                    transaction.clone(),
                                    symbol_table.clone(),
                                    transaction.next_stmt_mapping(),
                                    &self.ctx,
                                    trace,
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

                            self.print_scheduler_state(trace);

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
                        "Thread {:?} (`{}`) finished successfully, adding to `finished` queue",
                        thread.thread_id, thread.transaction.name
                    );

                    // If the thread's `end_time_step` is `None`, use the
                    // current `time_step` of the trace as a fallback.
                    // (In practice, `thread.end_time_step` will be
                    // set to `Some(...)` every time we encounter a `step()`
                    // in the program, and well-formedness constraints for our
                    // DSL dicatate that every function must contain at least one `step()`,
                    // so `thread.end_time_step` will always be `Some(...)` by the
                    // time we reach this point.)
                    let end_time_step = thread.end_time_step.unwrap_or_else(|| trace.time_step());

                    // Don't print out the inferred transaction if the user
                    // has marked it as `idle`
                    if self.interpreter.transaction.is_idle {
                        info!(
                            "Omitting idle transaction `{}` from trace",
                            self.interpreter.transaction.name
                        );
                    } else {
                        let transaction_str = self
                            .interpreter
                            .serialize_reconstructed_transaction(&self.ctx, trace);
                        // Add struct name prefix for multi-struct scenarios
                        let prefixed_transaction = if !self.struct_name.is_empty() {
                            format!("{}::{}", self.struct_name, transaction_str)
                        } else {
                            transaction_str
                        };
                        if self.ctx.show_waveform_time {
                            let start_time =
                                trace.format_time(thread.start_time_step, self.ctx.time_unit);
                            let end_time = trace.format_time(end_time_step, self.ctx.time_unit);
                            println!(
                                "{}  // [time: {} -> {}] (thread {})",
                                prefixed_transaction, start_time, end_time, thread.thread_id
                            );
                        } else {
                            println!("{}", prefixed_transaction)
                        }
                    }
                    self.finished.push(thread.clone());
                    break;
                }
                Err(err) => {
                    info!(
                        "Thread {} (`{}`) encountered `{}`, adding to `failed` queue",
                        thread.thread_id,
                        thread.transaction.name,
                        self.serialize_monitor_error(err, trace)
                    );
                    self.failed.push(thread);
                    self.print_scheduler_state(trace);
                    break;
                }
            }
        }
    }

    /// Pretty-prints an error message for the monitor
    /// (ExprIds/StmtIds are rendered with respect
    /// to a `Transaction` and `SymbolTable` in which they reside).
    /// Remarks:
    /// - At the moment, this function only adds extra information for
    ///   the `ValueDisagreesWithTrace` error message (this was used for debugging
    ///   the monitor). Otherwise, it falls-back on the error's `Display` instance.
    /// - We put this function here and not in `serialize.rs` of the
    ///   `protocols` crate, since it depends on some monitor-speciifc functionality
    ///   (e.g. whether to display the time of the error in time units or
    ///   in no. of cycles).
    pub fn serialize_monitor_error(&self, err: ExecutionError, trace: &WaveSignalTrace) -> String {
        match err {
            ExecutionError::Evaluation(EvaluationError::ValueDisagreesWithTrace {
                expr_id: _,
                value,
                trace_value,
                symbol_id,
                symbol_name,
                cycle_count,
            }) => {
                let time_str = if self.ctx.show_waveform_time {
                    trace.format_time(trace.time_step(), self.ctx.time_unit)
                } else {
                    format!("cycle {}", cycle_count)
                };

                format!(
                    "At {}: we expected {} ({}) to have value {}, but the trace value {} is different",
                    time_str,
                    symbol_name,
                    symbol_id,
                    serialize_bitvec(&value, false),
                    serialize_bitvec(&trace_value, false),
                )
            }
            _ => format!("{err}"),
        }
    }
}
