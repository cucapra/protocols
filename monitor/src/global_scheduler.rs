// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{
    global_context::GlobalContext,
    scheduler::Scheduler,
    signal_trace::{SignalTrace, StepResult, WaveSignalTrace},
};
use log::info;

pub struct GlobalScheduler {
    pub schedulers: Vec<Scheduler>,

    /// The waveform supplied by the user (shared across all schedulers)
    trace: WaveSignalTrace,
}

impl GlobalScheduler {
    /// Creates an new `GlobalScheduler`.
    /// Note: all the `Scheduler`s are expected to be initialized beforehand.
    pub fn new(schedulers: Vec<Scheduler>, trace: WaveSignalTrace) -> Self {
        Self { schedulers, trace }
    }

    /// Runs all the schedulers in a round-robin fashion
    pub fn run(&mut self, ctx: &GlobalContext) -> anyhow::Result<()> {
        if self.schedulers.is_empty() {
            return Ok(());
        }

        let mut trace_ended = false;

        loop {
            // Run each local scheduler's current phase
            for scheduler in self.schedulers.iter_mut() {
                // Note that individual schedulers can fail (which is OK
                // in a multi-struct setting, since there may not be
                // transactions for a particular struct that apply at a given
                // period in the waveform). Thus, we do `let _ = ...` here
                // to avoid an error in an individual scheduler
                // from causing the entire monitor executable to fail
                let _ = scheduler.run_current_phase(&self.trace, ctx);
            }

            // If we've reached the end of the trace,
            // print the final state of each individual scheduler,
            // then exit the loop
            if trace_ended {
                for scheduler in &self.schedulers {
                    if scheduler.next.is_empty() {
                        info!(
                            "Trace has ended, threads in `next` can't proceed, terminating scheduler for `{}` w/ final state:",
                            scheduler.struct_name
                        );
                        scheduler.print_scheduler_state(&self.trace, ctx);
                    }

                    // Print the no. of logical steps (clock cycles) taken
                    // by the scheduler if the corresponding CLI flag has been set
                    scheduler.print_step_count(ctx);
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
            for scheduler in self.schedulers.iter_mut() {
                info!(
                    "GlobalScheduler: Advancing scheduler for `{}` to the next cycle",
                    scheduler.struct_name
                );
                scheduler.advance_to_next_cycle(&ctx, &self.trace);
            }

            // Check if trace ended (if it finished, then we exit out the loop)
            if let StepResult::Done = step_result {
                info!("GlobalScheduler: No steps remaining in signal trace");
                // Mark all schedulers as having trace ended
                for scheduler in self.schedulers.iter_mut() {
                    scheduler.mark_trace_ended();
                }
                trace_ended = true;
            }
        }

        // No more threads to run in each of the schedulers
        info!("Monitor finished!");

        Ok(())
    }
}
