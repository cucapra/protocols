use anyhow::{Context, anyhow};
use baa::{BitVecOps, BitVecValue};
use log::info;
use protocols::{
    errors::{EvaluationError, ExecutionError},
    ir::{Expr, Stmt, StmtId, SymbolId, SymbolTable, Transaction},
    serialize::serialize_bitvec,
};
use rustc_hash::FxHashSet;

use crate::{
    global_context::GlobalContext,
    interpreter::Interpreter,
    queue::*,
    signal_trace::{SignalTrace, WaveSignalTrace},
    thread::Thread,
    types::{
        AugmentedProtocolApplication, AugmentedTrace, CycleResult, LoopArgState, SchedulerError,
        ThreadResult,
    },
};

/// Scheduler for handling the multiple threads in the monitor
#[derive(Clone)]
pub struct Scheduler {
    /// Queue storing threads that are ready (to be run during the current step)
    pub current: Queue,

    /// Queue of suspended threads (to be run during the next step)
    pub next: Queue,

    /// Threads that have finished successfully
    pub finished: Queue,

    /// Threads that failed
    pub failed: Queue,

    /// The current scheduling cycle
    pub cycle_count: u32,

    /// The no. of threads that have been created so far.
    /// (This variable is used to create unique `thread_id`s for `Thread`s.)
    pub num_threads: u32,

    /// The associated interpreter for Protocols programs
    interpreter: Interpreter,

    /// Flag indicating whether the trace has ended
    trace_ended: bool,

    /// Tracks which start cycles have already called fork() in the current cycle
    /// (Used to prevent duplicate thread spawning when multiple threads from the
    /// same start cycle finish simultaneously)
    forked_start_cycles: FxHashSet<u32>,

    /// Tracks which thread (if any) has finished in the current cycle
    /// Only one thread per struct should finish per cycle
    finished_thread: Option<(u32, u32, String)>, // (start_cycle, thread_id, transaction_name)

    /// All possible transactions (along with their corresponding `SymbolTable`s)
    /// (This is used when forking new threads)
    pub possible_transactions: Vec<(Transaction, SymbolTable)>,

    /// The name of the struct this scheduler is monitoring
    /// (Used for prefixing transaction names in multi-struct scenarios)
    /// Note: if there is just one single struct, this string is empty
    pub struct_name: String,

    /// Output buffer, where each element is an `OutputEntry`
    /// (defined in `types.rs`).
    pub output_buffer: AugmentedTrace,
}

impl Scheduler {
    // Helper function that prefixes a transaction's name with the name of a struct
    // if the source file contains multiple struct
    pub fn format_transaction_name(&self, ctx: &GlobalContext, transaction_name: String) -> String {
        if ctx.multiple_structs {
            format!("{}::{}", self.struct_name, transaction_name)
        } else {
            transaction_name
        }
    }

    /// Prints the internal state of the scheduler
    /// (i.e. the contents of all 4 queues + current scheduling cycle)
    pub fn print_scheduler_state(&self, trace: &WaveSignalTrace, ctx: &GlobalContext) {
        let time_step = trace.time_step();
        let header = if ctx.show_waveform_time {
            format!(
                "SCHEDULER STATE, TIME {}:",
                trace.format_time(time_step, ctx.time_unit)
            )
        } else {
            format!("SCHEDULER STATE, CYCLE {}:", self.cycle_count)
        };
        info!(
            "{}\n{}\n{}\n{}\n{}",
            header,
            format_args!(
                "Current: {}",
                format_queue(&self.current, ctx, trace, &self.struct_name)
            ),
            format_args!(
                "Next: {}",
                format_queue(&self.next, ctx, trace, &self.struct_name)
            ),
            format_args!(
                "Failed: {}",
                format_queue(&self.failed, ctx, trace, &self.struct_name)
            ),
            format_args!(
                "Finished: {}",
                format_queue(&self.finished, ctx, trace, &self.struct_name)
            )
        );
    }

    /// Initializes a `Scheduler` with one scheduled thread for each `(Transcation, SymbolTable)`
    /// pair in the argument `transactions`, along with a `GlobalContext` that is
    /// shared across all threads
    pub fn initialize(
        transactions: Vec<(Transaction, SymbolTable)>,
        ctx: &GlobalContext,
        trace: &WaveSignalTrace,
        struct_name: String,
        dut_symbol_id: SymbolId,
    ) -> Self {
        let cycle_count = 0;
        let mut thread_id = 0;
        let mut current_threads = Queue::new();
        // Create a new thread for each transaction, then push it to the
        // end of the `current` queue
        for (transaction, symbol_table) in &transactions {
            let thread = Thread::new(
                struct_name.clone(),
                transaction.clone(),
                symbol_table.clone(),
                transaction.next_stmt_mapping(),
                thread_id,
                cycle_count,
                trace.time_step(),
            );
            current_threads.push_back(thread);
            thread_id += 1;
        }
        // Technically, initializing the `interpreter` here is unnecessary
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
            ctx,
            trace,
            cycle_count,
            dut_symbol_id,
        );
        Self {
            current: current_threads,
            next: Queue::new(),
            finished: Queue::new(),
            failed: Queue::new(),
            interpreter,
            cycle_count,
            num_threads: thread_id,
            trace_ended: false,
            forked_start_cycles: FxHashSet::default(),
            finished_thread: None,
            possible_transactions: transactions,
            struct_name,
            output_buffer: Vec::new(),
        }
    }

    /// Call this function exactly once at the beginning of each cycle
    /// (**Don't** call this on a cloned `Scheduler` that is created from a `fork`)
    pub fn begin_cycle(&mut self, trace: &WaveSignalTrace, ctx: &GlobalContext) {
        // Clear auxiliary fields at the beginning of each cycle
        // to track which start cycles fork/finish in THIS cycle
        self.forked_start_cycles.clear();
        self.finished_thread = None;
        self.print_scheduler_state(trace, ctx);
    }

    /// Runs the scheduler in the current cycle by repeating the following steps.
    /// 1. While the `current` queue is non-empty,
    ///    pop a thread from the `current` queue and runs it till the next `step`
    ///    and exmaine its `ThreadResult`.
    ///  - If it `fork`ed either implicitly or explicitly, return early by
    ///    signalling to the caller the appropriate `CycleResult`
    ///  - Otherwise, continue.
    /// 2. When the `current` queue is empty, it sets `current` to `next`
    ///    (marking all suspended threads as ready for execution),
    ///    then advances the trace to the next step.
    ///    Notes:
    /// - This function is used by `GlobalScheduler::process_group_cycles`
    ///   to coordinate execution between multiple schedulers.
    /// - When a `fork` creates a `Scheduler` clone, call this function
    ///   on the clone
    pub fn process_current_queue(
        &mut self,
        trace: &WaveSignalTrace,
        ctx: &GlobalContext,
    ) -> Result<CycleResult, SchedulerError> {
        info!(
            "Inside `Scheduler::process_current_queue` for {} scheduler",
            self.struct_name
        );

        // Process each thread. Note that
        // this function returns early when a thread `fork`s, with the
        // new forked-off threads propagated to the caller
        // (`GlobalScheduler::process_group_cycles`)
        while let Some(thread) = self.current.pop_front() {
            match self.run_thread_till_next_step(thread, trace, ctx)? {
                ThreadResult::Completed => continue,
                ThreadResult::ExplicitFork { parent } => {
                    return Ok(CycleResult::Fork {
                        parent: Box::new(Some(*parent)),
                    });
                }
                ThreadResult::ImplicitFork => {
                    return Ok(CycleResult::Fork {
                        parent: Box::new(None),
                    });
                }
                ThreadResult::RepeatLoopFork {
                    exited_thread,
                    speculative_thread,
                } => {
                    return Ok(CycleResult::RepeatLoopFork {
                        exited_thread,
                        speculative_thread,
                    });
                }
            }
        }

        // At this point, all threads have been executed till their next `step`
        // and are synchronized (i.e. `current` is empty)

        // Check constraints for all threads in the `next` queue.
        // These threads have called `step()` and have more work to do.
        // Threads that finished (i.e. they executed the `step()` statement at
        // the end of a function) are not in `next`, so they won't be checked.
        let mut failed_constraint_checks = Vec::new();

        for thread in self.next.iter_mut() {
            // If any constraints failed, figure out the right time-step/cycle
            // to display in the logs
            let time_str = if ctx.show_waveform_time {
                trace.format_time(trace.time_step(), ctx.time_unit)
            } else {
                format!("cycle {}", self.interpreter.trace_cycle_count)
            };

            // Check that all constraints in the `constraints` map still hold
            // against the current trace values. This is called after each `step()`
            // to ensure that assignments like `D.m_axis_tvalid := 1'b1` continue
            // to hold after stepping to a new cycle.
            for (symbol_id, expected_value) in &thread.constraints {
                let symbol_name = thread.symbol_table.full_name_from_symbol_id(symbol_id);

                match trace.get(ctx.instance_id, *symbol_id) {
                    Ok(trace_value) => {
                        if trace_value != *expected_value {
                            info!(
                                "Constraint FAILED for thread {} (`{}`) at {}: {} = {} (trace) != {} (expected)",
                                thread.global_thread_id(ctx),
                                thread.transaction.name,
                                time_str,
                                symbol_name,
                                serialize_bitvec(&trace_value, ctx.display_hex),
                                serialize_bitvec(expected_value, ctx.display_hex)
                            );
                            failed_constraint_checks.push(thread.clone());
                        } else {
                            info!(
                                "Constraint OK for thread {} (`{}`) at {}: {} = {}",
                                thread.global_thread_id(ctx),
                                thread.transaction.name,
                                time_str,
                                symbol_name,
                                serialize_bitvec(expected_value, ctx.display_hex)
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
                    let time_str = if ctx.show_waveform_time {
                        trace.format_time(trace.time_step(), ctx.time_unit)
                    } else {
                        format!("cycle {}", self.interpreter.trace_cycle_count)
                    };

                    // Get the current port value from the trace
                    match trace.get(ctx.instance_id, *port_id) {
                        Ok(trace_value) => {
                            // Check whether all bits are known or if only
                            // some of them are known (e.g. due to a bit-slice)
                            let known_bits = thread
                                .known_bits
                                .get(param_id)
                                .ok_or_else(|| {
                                    anyhow!(
                                        "Unable to find {} in `known_bits` map of thread {} ({})",
                                        param_name,
                                        thread.global_thread_id(ctx),
                                        thread.transaction.name
                                    )
                                })
                                .context(format!("known_bits = {:?}", thread.known_bits))?;
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
                                        serialize_bitvec(&trace_value, ctx.display_hex),
                                        time_str
                                    );
                                    thread.args_mapping.insert(*param_id, trace_value);
                                } else {
                                    info!(
                                        "args_mapping OK: {} = {} = {}",
                                        param_name,
                                        port_name,
                                        serialize_bitvec(param_value, ctx.display_hex)
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
                failed_thread.global_thread_id(ctx),
                failed_thread.transaction.name
            );
            self.next.retain(|t| t.thread_id != failed_thread.thread_id);
            self.failed.push_back(failed_thread);
        }

        // Check that threads in the `finished` and `failed` queues
        // behave as expected
        self.validate_finished_and_failed_threads(trace, ctx)?;

        Ok(CycleResult::Done)
    }

    /// Validates that threads in the `finished` and `failed` queues
    /// behave as expected
    pub fn validate_finished_and_failed_threads(
        &mut self,
        trace: &WaveSignalTrace,
        ctx: &GlobalContext,
    ) -> Result<(), SchedulerError> {
        // Find the unique start cycles of all threads in the `finished` queue
        let finished_threads_start_cycles = unique_start_cycles(&self.finished);

        // Out of all threads that started in the same cycle & finished in the most recent step...
        for start_cycle in finished_threads_start_cycles {
            // ...there should only be at most one of them in `finished`
            let finished = threads_with_start_time(&self.finished, start_cycle);
            if finished.len() > 1 {
                let start_time = if ctx.show_waveform_time {
                    trace.format_time(finished[0].start_time_step, ctx.time_unit)
                } else {
                    format!("cycle {}", start_cycle)
                };
                let end_time_step = trace.time_step();
                let end_time = if ctx.show_waveform_time {
                    trace.format_time(end_time_step, ctx.time_unit)
                } else {
                    format!("cycle {}", self.cycle_count)
                };

                return Err(SchedulerError::Other(anyhow!(
                    "Scheduler for `{}`: Expected the no. of threads for that started at {} & ended at {} to be at most 1, but instead there were {} ({:?})",
                    self.struct_name,
                    start_time,
                    end_time,
                    finished.len(),
                    finished
                        .iter()
                        .map(|t| t.transaction.name.clone())
                        .collect::<Vec<_>>()
                )));
            }
            let finished_thread = &finished[0];

            // ...and there shouldn't be any other threads in `next`
            let next = threads_with_start_time(&self.next, start_cycle);
            if !next.is_empty() {
                let start_time_str = if ctx.show_waveform_time {
                    trace.format_time(finished_thread.start_time_step, ctx.time_unit)
                } else {
                    format!("cycle {}", finished_thread.start_cycle)
                };
                let error_context = anyhow!(
                    "Thread {} (`{}`) finished but there are other threads with the same start time ({}) in the `next` queue, namely {:?}",
                    finished_thread.global_thread_id(ctx),
                    finished_thread.transaction.name,
                    start_time_str,
                    next.iter()
                        .map(|t| t.transaction.name.clone())
                        .collect::<Vec<_>>()
                );

                return Err(SchedulerError::NoTransactionsMatch {
                    struct_name: self.struct_name.clone(),
                    error_context,
                });
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
            // an error. A thread `t` that started in an EARLIER cycle
            // might be paused at an intermediate `step()` (i.e. `t` is in `next`),
            // while all threads from the CURRENT `start_cycle` have failed.
            // In this case, we still need to try to run `t` since it may
            // succeed, even though all threads from the current cycle failed.
            // (Example: `picorv32/unsigned_mul.prot`)
            // We also check that no threads finished successfully this cycle
            // (regardless of their start cycle) before throwing the error --
            // this allows us to handle implicitly forked threads that
            // are spawned at the end of fork-free protocols (when they
            // reach the final `step()` statement).
            if failed.len() > 1
                && finished.is_empty()
                && paused.is_empty()
                && self.next.is_empty()
                && self.finished_thread.is_none()
            {
                let error_context = anyhow!(
                    "Out of all threads that started in cycle {}, all but one are expected to fail, but all {} of them failed",
                    start_cycle,
                    failed.len()
                );

                return Err(SchedulerError::NoTransactionsMatch {
                    struct_name: self.struct_name.clone(),
                    error_context,
                });
            }
        }

        // Print all the threads that finished & failed during the most recent step
        if !self.failed.is_empty() {
            if ctx.show_waveform_time {
                let time_str = trace.format_time(trace.time_step(), ctx.time_unit);
                info!(
                    "Threads that failed at time {}: {}",
                    time_str,
                    format_queue_compact(&self.failed, ctx)
                );
            } else {
                info!(
                    "Threads that failed in cycle {}: {}",
                    self.cycle_count,
                    format_queue_compact(&self.failed, ctx)
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
                return Err(SchedulerError::NoTransactionsMatch {
                    struct_name: self.struct_name.clone(),
                    error_context: anyhow!("All threads failed for {}", self.struct_name),
                });
            } else {
                self.failed.clear();
            }
        }

        if !self.finished.is_empty() {
            if ctx.show_waveform_time {
                let time_str = trace.format_time(trace.time_step(), ctx.time_unit);
                info!(
                    "Threads that finished at time {}: {}",
                    time_str,
                    format_queue_compact(&self.finished, ctx)
                );
            } else {
                info!(
                    "Threads that finished in cycle {}: {}",
                    self.cycle_count,
                    format_queue_compact(&self.finished, ctx)
                );
            }
            self.finished.clear();
        }

        Ok(())
    }

    /// Helper function to print the number of steps taken
    pub fn print_step_count(&self, ctx: &GlobalContext) {
        if ctx.print_num_steps {
            eprintln!(
                "No. of steps taken by {} scheduler: {}",
                self.struct_name, self.cycle_count
            );
        }
    }

    /// Advances to the next cycle by moving next queue to current and incrementing cycle count
    /// (This function should only be called after `trace.step()` has been called in `GlobalScheduler`)
    pub fn advance_to_next_cycle(&mut self, ctx: &GlobalContext, trace: &WaveSignalTrace) {
        // If next queue is empty and we're in multi-struct mode,
        // spawn new threads for this cycle.
        // This is necessary in multi-struct mode where schedulers need to continuously
        // try to discover transactions even if all previous threads failed
        if self.next.is_empty() && ctx.multiple_structs {
            info!(
                "Next queue is empty for `{}` scheduler, spawning new threads for cycle {}",
                self.struct_name, self.cycle_count
            );
            for (transaction, symbol_table) in &self.possible_transactions {
                let new_thread = Thread::new(
                    self.struct_name.clone(),
                    transaction.clone(),
                    symbol_table.clone(),
                    transaction.next_stmt_mapping(),
                    self.num_threads,
                    self.cycle_count,
                    trace.time_step(),
                );
                self.num_threads += 1;
                info!(
                    "Adding new thread {} (`{}`) to `next` queue",
                    new_thread.global_thread_id(ctx),
                    self.format_transaction_name(ctx, new_thread.transaction.name.clone())
                );
                self.next.push_back(new_thread);
            }
        }

        // Mark all suspended threads as ready for execution
        // by setting `current` to `next`, and setting `next = []`
        // (the latter is done via `std::mem::take`)
        self.current = std::mem::take(&mut self.next);
        self.cycle_count += 1;
        self.interpreter.trace_cycle_count += 1;

        if ctx.show_waveform_time {
            let time_str = trace.format_time(trace.time_step(), ctx.time_unit);
            info!("Advancing to time {}, setting current = next", time_str);
        } else {
            info!(
                "Advancing to cycle {}, setting current = next",
                self.cycle_count
            );
        }
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
    pub fn emit_error(&self, trace: &WaveSignalTrace, ctx: &GlobalContext) -> anyhow::Result<()> {
        self.print_step_count(ctx);
        let time_str = if ctx.show_waveform_time {
            trace.format_time(trace.time_step(), ctx.time_unit)
        } else {
            format!("cycle {}", self.interpreter.trace_cycle_count)
        };

        let error_msg = anyhow!(
            "Failure at {}: No transactions match the waveform in `{}`.\nPossible transactions: [{}]",
            time_str,
            ctx.waveform_file,
            self.possible_transactions
                .iter()
                .map(|(tr, _)| tr.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        );
        Err(error_msg)
    }

    /// Helper function which handles `repeat` loops by forking two threads:
    /// - One which exits the loop with the `LoopArg` set to `Known(n)`
    /// - One which speculatively executes the loop body for another iteration,
    ///   with the `LoopArg` set to `Speculative(n + 1)`
    ///
    /// The arguments to this function are:
    /// - The `SymbolId` / `StmtId`s of the `LoopArg`, loop body and the
    ///   entire loop statement itself
    /// - The `current_thread` (which will speculatively execute the loop body
    ///   for another iteration)
    /// - The value `n` that has been currently "guessed" for the `LoopArg`
    ///
    /// This function returns a `ThreadResult::RepeatLoopFork` containing the
    /// two threads.
    fn handle_repeat_loops(
        &mut self,
        loop_arg_symbol_id: SymbolId,
        loop_body_id: StmtId,
        loop_stmt_id: StmtId,
        mut current_thread: Thread,
        n: u64,
    ) -> ThreadResult {
        // Create a new thread `exited_thread` that is identical
        // to the current thread, but it exits the loop
        // with the `LoopArg` set to `Known(n)`
        let mut exited_thread = current_thread.clone();
        exited_thread.thread_id = self.num_threads;
        self.num_threads += 1;
        exited_thread
            .loop_args_state
            .insert(loop_arg_symbol_id, LoopArgState::Known(n));

        // Also add the `loop_arg` to the `exited_thread`'s
        // `args_mapping` and `known_bits` map.
        // (The `loop_arg` is an input
        // parameter, so other statements in the protocol
        // can still refer to it)
        let loop_arg_bitwidth = current_thread.symbol_table[loop_arg_symbol_id]
            .tpe()
            .bitwidth();
        exited_thread.args_mapping.insert(
            loop_arg_symbol_id,
            BitVecValue::from_u64(n, loop_arg_bitwidth),
        );
        exited_thread
            .known_bits
            .insert(loop_arg_symbol_id, BitVecValue::ones(loop_arg_bitwidth));

        // The exited_thread needs to execute the first statement
        // that immediately follow the loop
        exited_thread.current_stmt_id = self.interpreter.next_stmt_map[&loop_stmt_id].expect(
                            "Repeat loops can't be the last statement in a protocol since protocols always end with `step`"
                        );

        // Update the current thread's `loop_args` map so that
        // the `LoopArg` is now `Speculative(n + 1)`
        current_thread.loop_args_state.insert(
            loop_arg_symbol_id,
            LoopArgState::Speculative(n + 1, loop_stmt_id),
        );

        // The current thread executes the
        // loop body for another iteration speculatively
        current_thread.current_stmt_id = loop_body_id;

        // Let the global scheduler deal with both threads
        // (The current thread is called the `speculative_thread`,
        // since it speculatively executes the loop body again
        // with the `LoopArg` set to `Speculative(n + 1)`)
        ThreadResult::RepeatLoopFork {
            exited_thread: Box::new(exited_thread),
            speculative_thread: Box::new(current_thread),
        }
    }

    /// Keeps running a `thread` until:
    /// - It reaches the next `step()` or `fork()` statement
    /// - It completes succesfully
    /// - An error was encountered during execution
    pub fn run_thread_till_next_step(
        &mut self,
        mut thread: Thread,
        trace: &WaveSignalTrace,
        ctx: &GlobalContext,
    ) -> Result<ThreadResult, SchedulerError> {
        info!(
            "Running thread {} (transaction `{}`) till next `step()`...",
            thread.global_thread_id(ctx),
            self.format_transaction_name(ctx, thread.transaction.name.clone())
        );

        // Perform a context switch (use the argument thread's `Transaction`
        // & associated `SymbolTable` / `NextStmtMap`)
        self.interpreter.context_switch(&thread);

        let mut current_stmt_id = thread.current_stmt_id;

        loop {
            // Intercept repeat loops before evaluating statements
            if let Stmt::RepeatLoop(loop_arg_expr_id, loop_body_id) =
                thread.transaction[current_stmt_id]
            {
                let loop_stmt_id = current_stmt_id;
                let loop_arg_symbol_id = match thread.transaction[loop_arg_expr_id] {
                    Expr::Sym(symbol_id) => symbol_id,
                    Expr::Const(_) => {
                        todo!("Maybe allow constants to appear as arguments to repeat loops??")
                    }
                    _ => {
                        unreachable!("Arguments to repeat loops are always SymbolIDs")
                    }
                };

                // Suppose we already know how many iterations a `repeat` loop
                // must take. If so, we execute it deterministically.
                // This situation occurs if there are multiple `repeat` loops
                // in a protocol that use the same `LoopArg`, e.g.
                // `repeat n iterations { ... }; ...; repeat n iterations { ... }`
                if let Some(num_remaining_iters) =
                    thread.repeat_loops_remaining_iters.get_mut(&loop_stmt_id)
                {
                    *num_remaining_iters -= 1;
                    if *num_remaining_iters == 0 {
                        thread.repeat_loops_remaining_iters.remove(&loop_stmt_id);
                        current_stmt_id = self.interpreter.next_stmt_map[&loop_stmt_id].expect(
                            "Repeat loops can't be the last statement in a protocol since protocols always end with `step()`"
                        );
                    } else {
                        current_stmt_id = loop_body_id;
                    }
                    continue;
                }

                // Now we need to handle the case when the value of a `LoopArg`
                // is unknown
                match thread.loop_args_state.get(&loop_arg_symbol_id).cloned() {
                    None => {
                        // First time seeing loop arg, it is `Unknown`
                        // (i.e. absent from the thread's `loop_args_state` map),
                        // so pass in `n = 0` to the `handle_repeat_loops`
                        // helper function
                        return Ok(self.handle_repeat_loops(
                            loop_arg_symbol_id,
                            loop_body_id,
                            loop_stmt_id,
                            thread,
                            0,
                        ));
                    }
                    Some(LoopArgState::Speculative(n, stored_loop_stmt_id)) => {
                        // We disallow nested `repeat` loops that use the
                        // same loop argument, i.e. we forbid
                        // `repeat n iterations { repeat n iterations { ... } ... }`
                        if loop_stmt_id != stored_loop_stmt_id {
                            panic!(
                                "Nested `repeat` loops that use the same loop argument `{}` are forbidden",
                                thread.symbol_table[loop_arg_symbol_id].name()
                            )
                        }

                        // Fork two threads:
                        // one with `Known(n)`, one with `Speculative(n + 1)`
                        return Ok(self.handle_repeat_loops(
                            loop_arg_symbol_id,
                            loop_body_id,
                            loop_stmt_id,
                            thread,
                            n,
                        ));
                    }
                    Some(LoopArgState::Known(n)) => {
                        // Value of `n` has been resolved from a prior loop
                        // (either with the same `StmtId` or a different `StmtId`)
                        if n == 0 {
                            // Exit the loop since the `LoopArg` is already known,
                            // proceed to the next immediate statement
                            // (evaluated in the next iteration
                            // of the outer `loop` in this function)
                            current_stmt_id = self.interpreter.next_stmt_map[&loop_stmt_id].expect(
                                "Repeat loops can't be the last statement in a protocol since protocols always end with `step()`"
                            );
                        } else {
                            // Insert it into the thread's `repeat_loops_remaining_iters`
                            // map, which tracks how many iterations need to be executed
                            // for this loop
                            thread.repeat_loops_remaining_iters.insert(loop_stmt_id, n);
                            current_stmt_id = loop_body_id;
                        }
                        continue;
                    }
                }
            }
            match self.interpreter.evaluate_stmt(&current_stmt_id, ctx, trace) {
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
                                "Thread {} (transaction `{}`) called `step()`, moving to `next` queue",
                                thread.global_thread_id(ctx),
                                thread.transaction.clone().name,
                            );

                            // if the thread is moving to the `next` queue,
                            // its `current_stmt_id` is updated to be `next_stmt_id`
                            thread.current_stmt_id = next_stmt_id;
                            self.next.push_back(thread);
                            self.print_scheduler_state(trace, ctx);
                            return Ok(ThreadResult::Completed);
                        }
                        Stmt::Fork => {
                            thread.has_forked = true;

                            // Check if another thread from the same start cycle has already forked
                            // in the current cycle for this scheduler.
                            // If so, skip the fork to avoid creating duplicate threads.
                            let already_forked =
                                self.forked_start_cycles.contains(&thread.start_cycle);

                            if already_forked {
                                info!(
                                    "Thread {} called `fork()`, but another thread from the same start cycle (cycle {}) already forked in this cycle. Skipping fork to avoid duplicates.",
                                    thread.global_thread_id(ctx),
                                    thread.start_cycle
                                );
                                // Continue from the fork statement onwards
                                current_stmt_id = next_stmt_id;
                            } else {
                                // Here, instead of creating a new thread for
                                // each possible protocol, we indicate to the
                                // caller that the current thread forked

                                // Indicate that the thread's `start_cycle`
                                // called `fork` in the current cycle
                                self.forked_start_cycles.insert(thread.start_cycle);

                                // Advance to next statement
                                thread.current_stmt_id = next_stmt_id;

                                // Save the parent thread's state before we exit this function
                                thread.args_mapping = self.interpreter.args_mapping.clone();
                                thread.known_bits = self.interpreter.known_bits.clone();
                                thread.constraints = self.interpreter.constraints.clone();
                                thread.args_to_pins = self.interpreter.args_to_pins.clone();

                                // Indicate to the caller that this thread forked
                                return Ok(ThreadResult::ExplicitFork {
                                    parent: Box::new(thread),
                                });
                            }
                        }
                        _ => {
                            // Default case: update `current_stmt_id`
                            // to point to `next_stmt_id`
                            current_stmt_id = next_stmt_id;
                        }
                    }
                }
                Ok(None) => {
                    // Check if another thread has already finished in this cycle.
                    // Invariant: Only one thread per struct can finish per cycle
                    if let Some((first_start_cycle, first_thread_id, first_transaction_name)) =
                        &self.finished_thread
                    {
                        info!(
                            "Thread {} (`{}`) would have finished, but another thread (thread {} `{}` from start_cycle {}) already finished in this cycle. Marking as failed.",
                            thread.global_thread_id(ctx),
                            self.format_transaction_name(ctx, thread.transaction.name.clone()),
                            first_thread_id,
                            self.format_transaction_name(ctx, first_transaction_name.to_string()),
                            first_start_cycle
                        );
                        self.failed.push_back(thread);
                        self.print_scheduler_state(trace, ctx);
                        return Ok(ThreadResult::Completed);
                    }

                    info!(
                        "Thread {} (`{}`) finished successfully, adding to `finished` queue",
                        thread.global_thread_id(ctx),
                        self.format_transaction_name(ctx, thread.transaction.name.clone())
                    );

                    // Record this thread as having finished in this cycle
                    self.finished_thread = Some((
                        thread.start_cycle,
                        thread.thread_id,
                        thread.transaction.name.clone(),
                    ));

                    // Use the actual time-step from the waveform as the `end_time_step`
                    let end_time_step = trace.time_step();

                    // Construct a `ProtocolApplication` object
                    // from the current interpreter state
                    // (i.e. an entry in the monitor's output trace)
                    let struct_name = if ctx.multiple_structs {
                        Some(self.struct_name.clone())
                    } else {
                        None
                    };
                    let is_idle = self.interpreter.transaction.is_idle;
                    let protocol_application =
                        self.interpreter
                            .to_protocol_application(struct_name, ctx, trace);

                    if is_idle {
                        info!(
                            "Transaction `{}` is marked as idle",
                            self.interpreter.transaction.name
                        );
                    }

                    // Add the output entry + metadata to the scheduler's
                    // output buffer
                    self.output_buffer.push(AugmentedProtocolApplication {
                        end_cycle_count: self.cycle_count,
                        protocol_application,
                        start_time_step: thread.start_time_step,
                        end_time_step,
                        thread_id: thread.global_thread_id(ctx),
                        is_idle,
                    });
                    self.finished.push_back(thread.clone());

                    // Implicit fork: if this thread hasn't forked yet,
                    // indicate to the caller that an implicit fork
                    // needs to be performed.
                    // This handles the case where a protocol just ends in
                    // `step()` without having previously called `fork()`
                    if !thread.has_forked {
                        info!(
                            "Thread {} finished without explicit fork, performing implicit fork",
                            thread.global_thread_id(ctx)
                        );
                        self.forked_start_cycles.insert(thread.start_cycle);
                        return Ok(ThreadResult::ImplicitFork);
                    } else {
                        return Ok(ThreadResult::Completed);
                    }
                }
                Err(err) => {
                    info!(
                        "Thread {} (`{}`) encountered `{}`, adding to `failed` queue",
                        thread.global_thread_id(ctx),
                        self.format_transaction_name(ctx, thread.transaction.name.clone()),
                        self.serialize_monitor_error(err, trace, ctx)
                    );
                    self.failed.push_back(thread);
                    self.print_scheduler_state(trace, ctx);
                    return Ok(ThreadResult::Completed);
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
    pub fn serialize_monitor_error(
        &self,
        err: ExecutionError,
        trace: &WaveSignalTrace,
        ctx: &GlobalContext,
    ) -> String {
        match err {
            ExecutionError::Evaluation(EvaluationError::ValueDisagreesWithTrace {
                expr_id: _,
                value,
                trace_value,
                symbol_id,
                symbol_name,
                cycle_count,
            }) => {
                let time_str = if ctx.show_waveform_time {
                    trace.format_time(trace.time_step(), ctx.time_unit)
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
