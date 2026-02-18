// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::collections::VecDeque;

use crate::{
    global_context::GlobalContext,
    scheduler::Scheduler,
    signal_trace::{SignalTrace, StepResult, WaveSignalTrace},
    thread::Thread,
    types::{
        AugmentedProtocolApplication, AugmentedTrace, CycleResult, SchedulerError, SchedulerGroup,
        Trace,
    },
};
use log::info;
use rustc_hash::FxHashSet;

pub struct GlobalScheduler {
    /// Each element in the outer `Vec` corresponds to a `struct`.
    /// Each element in the inner `VecDeque` is a scheduler clone
    /// (which explores different possible protocol traces).
    pub scheduler_groups: Vec<SchedulerGroup>,

    /// The waveform supplied by the user (shared across all schedulers)
    trace: WaveSignalTrace,
}

/// Processes one clock cycle for all schedulers within the same scheduler group
/// (See `types.rs` for the definition of a *scheduler group*)
fn process_group_cycles(
    scheduler_group: SchedulerGroup,
    trace: &WaveSignalTrace,
    ctx: &GlobalContext,
) -> anyhow::Result<SchedulerGroup> {
    // We have to define this up here since we end up mutating `scheduler_group`
    // later in this function
    let group_was_non_empty = !scheduler_group.is_empty();

    // BFS queue of schedulers (each scheduler represents the continuation
    // of a possible protocol trace)
    let mut last_failed_scheduler: Option<Scheduler> = None;
    let mut schedulers_to_process: SchedulerGroup = scheduler_group;
    let mut processed_schedulers: SchedulerGroup = SchedulerGroup::new();

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

/// For a single scheduler group, collects all unique maximal traces
/// (deduplicated on canonical `ProtocolApplication` sequence, excluding idle,
/// with strict-prefix traces filtered out).
/// Returns the list of maximal `AugmentedProtocolApplication` traces for this group.
fn collect_maximal_traces(scheduler_group: &SchedulerGroup) -> Vec<AugmentedTrace> {
    // Collect all unique traces, deduplicating on the canonical
    // `ProtocolApplication` sequence (ignoring timing and thread IDs)
    let mut all_entries: Vec<AugmentedTrace> = vec![];
    let mut seen_traces: FxHashSet<Trace> = FxHashSet::default();

    for scheduler in scheduler_group {
        // Sort `AugmentedProtocolApplication`s by increasing cycle no.
        let mut sorted_output_entries = scheduler.output_buffer.clone();
        sorted_output_entries.sort_by_key(|prot| prot.end_cycle_count);

        // Build canonical trace for dedup, excluding idle entries
        let trace: Trace = sorted_output_entries
            .iter()
            .filter(|prot| !prot.is_idle)
            .map(|prot| prot.protocol_application.clone())
            .collect();

        // Only append `sorted_output_entries` to `all_entries`
        // if it the corresponding `trace` wasn't previously in `seen_traces`
        if seen_traces.insert(trace) {
            all_entries.push(sorted_output_entries);
        }
    }

    // Filter out traces that are strict prefixes of other traces.
    // These are partial traces from schedulers where a child thread failed
    // but the parent thread completed successfully,
    // resulting in a shorter trace.
    let all_traces: Vec<Trace> = all_entries
        .iter()
        .map(|augmented_trace| {
            augmented_trace
                .iter()
                .filter(|prot| !prot.is_idle)
                .map(|prot| prot.protocol_application.clone())
                .collect()
        })
        .collect();

    // Filter out strict prefix traces
    all_entries
        .into_iter()
        .enumerate()
        .filter(|(i, _)| {
            !all_traces.iter().any(|other| {
                other.len() > all_traces[*i].len() && other.starts_with(all_traces[*i].as_slice())
            })
        })
        .map(|(_, entries)| entries)
        .collect()
}

impl GlobalScheduler {
    /// Pretty-prints a `trace { ... }` block to stdout
    fn print_trace_block(trace_index: usize, lines: &[String]) {
        println!("// trace {}", trace_index);
        println!("trace {{");
        for line in lines {
            println!("    {}", line);
        }
        println!("}}");
    }

    /// Creates an new `GlobalScheduler`.
    /// Note: all the `Scheduler`s are expected to be initialized beforehand.
    pub fn new(schedulers: Vec<Scheduler>, trace: WaveSignalTrace) -> Self {
        let scheduler_groups: Vec<SchedulerGroup> = schedulers
            .into_iter()
            .map(|s| VecDeque::from(vec![s]))
            .collect();
        Self {
            scheduler_groups,
            trace,
        }
    }

    /// Prints all unique protocol traces across all scheduler groups.
    /// (Recall that a scheduler group is just all schedulers corresponding
    /// to the same `struct` in our DSL, where each scheduler is responsible
    /// for exploring a possible candidate protocol trace.)
    /// For multi-struct protocols, each struct's scheduler group is processed
    /// independently during BFS, then the maximal (longest) trace from each
    /// group is interleaved by cycle count at display time.
    pub fn print_all_traces(&self, ctx: &GlobalContext) {
        // Collect the maximal traces per scheduler group.
        // The inner `Vec` represents the traces for all the schedulers
        // for the same struct, while the outer `Vec` iterates over all
        // possible `struct`s in the user-supplied `.prot` file.
        let mut scheduler_group_traces: Vec<Vec<AugmentedTrace>> = self
            .scheduler_groups
            .iter()
            .map(collect_maximal_traces)
            .collect();

        if scheduler_group_traces.is_empty() {
            return;
        }

        // Closure for deduplicating traces based on whether
        // protocols have been annotated with `#[idle]` and if
        // the monitor is in `always_include_idle` mode
        let filter_key =
            |prot_app: &AugmentedProtocolApplication| ctx.always_include_idle || !prot_app.is_idle;

        // For single-struct: show all unique traces directly
        if scheduler_group_traces.len() == 1 {
            // We call `swap_remove` to take ownership of
            // `scheduler_group_traces[0]` without cloning.
            // Since we only enter this branch when there's 1 element in
            // `scheduler_group_traces`, calling `swap_remove` is OK
            // (doesn't break functionality).
            let traces: Vec<AugmentedTrace> = scheduler_group_traces.swap_remove(0);
            for (i, trace) in traces.into_iter().enumerate() {
                let lines: Vec<String> = trace
                    .into_iter()
                    .filter(filter_key)
                    .map(|entry| self.format_augmented_protocol_application(&entry, ctx))
                    .collect();
                if i > 0 {
                    println!();
                }
                Self::print_trace_block(i, &lines);
            }
            return;
        }

        // If we have multiple structs, pick the longest trace from each scheduler
        // group. Interleave traces from each struct based on the cycle count in order.
        let mut merged: AugmentedTrace = vec![];
        for group in scheduler_group_traces.into_iter() {
            if let Some(longest) = group
                .into_iter()
                .max_by_key(|t| t.iter().filter(|&x| filter_key(x)).count())
            {
                merged.extend(longest.clone());
            }
        }
        merged.sort_by_key(|entry| entry.end_cycle_count);

        // Format for stdout
        let lines: Vec<String> = merged
            .into_iter()
            .filter(filter_key)
            .map(|entry| self.format_augmented_protocol_application(&entry, ctx))
            .collect();
        Self::print_trace_block(0, &lines);
    }

    /// Formats an `AugmentedProtocolApplication` into a display string
    fn format_augmented_protocol_application(
        &self,
        entry: &AugmentedProtocolApplication,
        ctx: &GlobalContext,
    ) -> String {
        match (ctx.show_waveform_time, ctx.show_thread_ids) {
            (true, true) | (true, false) => {
                let start_time = self.trace.format_time(entry.start_time_step, ctx.time_unit);
                let end_time = self.trace.format_time(entry.end_time_step, ctx.time_unit);
                if ctx.show_thread_ids {
                    format!(
                        "{};  // [time: {} -> {}] (thread {})",
                        entry.protocol_application, start_time, end_time, entry.thread_id
                    )
                } else {
                    format!(
                        "{};  // [time: {} -> {}]",
                        entry.protocol_application, start_time, end_time
                    )
                }
            }
            (false, true) => format!(
                "{};  // (thread {})",
                entry.protocol_application, entry.thread_id
            ),
            (false, false) => format!("{};", entry.protocol_application),
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
        self.print_all_traces(ctx);

        Ok(())
    }
}
