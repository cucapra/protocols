// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::collections::VecDeque;

use crate::{
    global_context::GlobalContext,
    scheduler::{CycleResult, Scheduler, SchedulerError},
    signal_trace::{SignalTrace, StepResult, WaveSignalTrace},
    thread::Thread,
};
use log::info;
use rustc_hash::FxHashSet;

pub struct GlobalScheduler {
    /// Each element in the outer `Vec` corresponds to a `struct`.
    /// Each element in the inner `VecDeque` is a scheduler clone
    /// (which explores different possible protocol traces).
    pub scheduler_groups: Vec<VecDeque<Scheduler>>,

    /// The waveform supplied by the user (shared across all schedulers)
    trace: WaveSignalTrace,
}

/// Processes one cycle for a *scheduler group*
/// (the collection of all schedulers corresponding to the same struct,
/// where each scheduler represents a different possible protocol trace)
fn process_group_cycles(
    scheduler_group: VecDeque<Scheduler>,
    trace: &WaveSignalTrace,
    ctx: &GlobalContext,
) -> anyhow::Result<VecDeque<Scheduler>> {
    // We have to define this up here since we end up mutating `scheduler_group`
    // later in this function
    let group_was_non_empty = !scheduler_group.is_empty();

    // BFS queue of schedulers (each scheduler represents the continuation
    // of a possible protocol trace)
    let mut last_failed_scheduler: Option<Scheduler> = None;
    let mut schedulers_to_process: VecDeque<Scheduler> = scheduler_group;
    let mut processed_schedulers: VecDeque<Scheduler> = VecDeque::new();

    while let Some(mut scheduler) = schedulers_to_process.pop_front() {
        match scheduler.process_current_queue(trace, ctx) {
            Ok(CycleResult::Done) => processed_schedulers.push_back(scheduler),
            Ok(CycleResult::Fork { parent }) => {
                // Iterate over all possible candidate protocols
                for (transaction, symbol_table) in &scheduler.possible_transactions {
                    let mut cloned_scheduler = scheduler.clone();

                    // If there was an explicit fork, we have to add the
                    // parent thread to the cloned scheduler
                    if let Some(ref thread) = *parent {
                        cloned_scheduler.current.push_front(thread.clone());
                    }

                    // Create a new thread for the candidate protocol
                    let new_thread = Thread::new(
                        cloned_scheduler.struct_name.clone(),
                        transaction.clone(),
                        symbol_table.clone(),
                        transaction.next_stmt_mapping(),
                        cloned_scheduler.num_threads,
                        cloned_scheduler.cycle_count,
                        trace.time_step(),
                    );
                    cloned_scheduler.num_threads += 1;
                    cloned_scheduler.current.push_back(new_thread);

                    // Continue processing the cloned scheduler
                    schedulers_to_process.push_back(cloned_scheduler);
                }
            }
            Err(SchedulerError::NoTransactionsMatch {
                struct_name,
                error_context,
            }) => {
                // This individual scheduler failed, so we discard it
                // (Other schedulers in the scheduler group may still succeed)
                info!(
                    "Error in scheduler for {}: {:#}",
                    struct_name, error_context
                );
                last_failed_scheduler = Some(scheduler);
            }
            Err(SchedulerError::Other(err)) => {
                // This individual scheduler failed; discard it.
                info!("Scheduler error for `{}`: {:#}", scheduler.struct_name, err);
                last_failed_scheduler = Some(scheduler);
            }
        }
    }

    // If all schedulers in the scheduler group failed, emit the error
    if group_was_non_empty && processed_schedulers.is_empty() {
        if let Some(failed_scheduler) = &last_failed_scheduler {
            eprintln!(
                "All schedulers failed: No transactions match the waveform for DUT `{}`",
                failed_scheduler.struct_name
            );
            failed_scheduler.emit_error(trace, ctx)?;
        }
    }

    Ok(processed_schedulers)
}

impl GlobalScheduler {
    /// Creates an new `GlobalScheduler`.
    /// Note: all the `Scheduler`s are expected to be initialized beforehand.
    pub fn new(schedulers: Vec<Scheduler>, trace: WaveSignalTrace) -> Self {
        let scheduler_groups: Vec<VecDeque<Scheduler>> = schedulers
            .into_iter()
            .map(|s| VecDeque::from(vec![s]))
            .collect();
        Self {
            scheduler_groups,
            trace,
        }
    }

    /// Prints all unique protocol traces across all scheduler groups.
    /// Each scheduler's `output_buffer` represents one possible trace.
    /// Identical traces are removed, and partial traces that are
    /// strict prefixes of longer traces are filtered out (these come from
    /// schedulers where the child thread failed but the parent thread
    /// continued).
    pub fn print_all_traces(&self) {
        // Collect all unique traces
        let mut all_traces: Vec<Vec<String>> = vec![];
        let mut seen = FxHashSet::default();

        for scheduler_group in &self.scheduler_groups {
            for scheduler in scheduler_group {
                let mut sorted_buffer = scheduler.output_buffer.clone();
                sorted_buffer.sort_by_key(|(cycle_count, _)| *cycle_count);

                let trace: Vec<String> = sorted_buffer
                    .iter()
                    .map(|(_, output)| output.clone())
                    .collect();

                if seen.insert(trace.clone()) {
                    all_traces.push(trace);
                }
            }
        }

        // Filter out traces that are strict prefixes of other traces.
        // These are partial traces from schedulers where a child thread failed
        // but the parent thread completed successfully,
        // resulting in a shorter trace.
        let maximal_traces: Vec<&Vec<String>> = all_traces
            .iter()
            .filter(|trace| {
                !all_traces
                    .iter()
                    .any(|other| other.len() > trace.len() && other.starts_with(trace.as_slice()))
            })
            .collect();

        if maximal_traces.is_empty() {
            return;
        }

        // Print all the traces one after another
        for (i, trace) in maximal_traces.iter().enumerate() {
            if maximal_traces.len() > 1 {
                println!("Trace {}:", i);
            }
            println!("{}", trace.join("\n"));
        }
    }

    /// Runs all the schedulers in a round-robin fashion
    pub fn run(&mut self, ctx: &GlobalContext) -> anyhow::Result<()> {
        if self.scheduler_groups.is_empty() {
            return Ok(());
        }

        let mut trace_ended = false;

        loop {
            for scheduler_group in self.scheduler_groups.iter_mut() {
                // Begin cycle for each schedulers in all scheduler groups
                for scheduler in scheduler_group.iter_mut() {
                    scheduler.begin_cycle(&self.trace, ctx);
                }

                // Process each scheduler group and handle forks
                let schedulers = std::mem::take(scheduler_group);
                *scheduler_group = process_group_cycles(schedulers, &self.trace, ctx)?;
            }

            // If we've reached the end of the trace,
            // print the final state of each individual scheduler,
            // then exit the loop
            if trace_ended {
                for scheduler_group in &self.scheduler_groups {
                    for scheduler in scheduler_group {
                        if scheduler.next.is_empty() {
                            info!(
                                "Trace has ended, threads in `next` can't proceed, terminating scheduler for `{}` w/ final state:",
                                scheduler.struct_name
                            );
                            scheduler.print_scheduler_state(&self.trace, ctx);
                        }
                        scheduler.print_step_count(ctx);
                    }
                }
                break;
            }

            // Advance the trace (only once for all schedulers)
            let step_result = self.trace.step();

            if ctx.show_waveform_time {
                let time_str = self
                    .trace
                    .format_time(self.trace.time_step(), ctx.time_unit);
                info!("GlobalScheduler: Advancing to time {}", time_str);
            } else {
                info!("GlobalScheduler: Advancing to next cycle");
            }

            // Advance all schedulers to their next cycle
            for scheduler_group in self.scheduler_groups.iter_mut() {
                for scheduler in scheduler_group.iter_mut() {
                    info!(
                        "GlobalScheduler: Advancing scheduler for `{}` to the next cycle",
                        scheduler.struct_name
                    );
                    scheduler.advance_to_next_cycle(ctx, &self.trace);
                }
            }

            // Check if trace ended (if it finished, then we exit out the loop)
            if let StepResult::Done = step_result {
                info!("GlobalScheduler: No steps remaining in signal trace");
                // Mark all schedulers as having trace ended
                for scheduler_group in self.scheduler_groups.iter_mut() {
                    for scheduler in scheduler_group.iter_mut() {
                        scheduler.mark_trace_ended();
                    }
                }
                trace_ended = true;
            }
        }

        // No more threads to run in each of the schedulers
        info!("Monitor finished!");

        // Print all collected traces
        self.print_all_traces();

        Ok(())
    }
}
