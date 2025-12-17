// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{global_context::GlobalContext, scheduler::Scheduler, signal_trace::WaveSignalTrace};

struct GlobalScheduler {
    schedulers: Vec<Scheduler>,
    ctx: GlobalContext,
    trace: WaveSignalTrace,
}

impl GlobalScheduler {
    pub fn new(schedulers: Vec<Scheduler>, ctx: GlobalContext, trace: WaveSignalTrace) -> Self {
        Self {
            schedulers,
            ctx,
            trace,
        }
    }

    // TODO: figure out how to initialize all schedulers
}
