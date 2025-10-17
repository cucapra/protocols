// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use crate::thread::Thread;

/// Queue of threads
type Queue = Vec<Thread>;

/// Extracts all elements in the `Queue` where all the threads have the
/// same `start_cycle`, preserving their order
pub fn threads_with_start_time(queue: Queue, start_cycle: usize) -> Queue {
    queue
        .into_iter()
        .filter(|thread| thread.start_cycle == start_cycle)
        .collect()
}

pub struct Scheduler {
    /// Queue storing threads that are ready (to be run during the current step)
    ready_threads: Queue,

    /// Queue of suspended threads (to be run during the next step)
    suspended_threads: Queue,

    /// Threads that have completed successfully
    completed_threads: Queue,

    /// Threads that failed
    failed_threads: Queue,
}

impl Scheduler {
    /// Creates a new `Scheduler` where all four queues are empty
    pub fn new() -> Self {
        Self {
            ready_threads: vec![],
            suspended_threads: vec![],
            completed_threads: vec![],
            failed_threads: vec![],
        }
    }

    // TODO: figure out how to run a thread till the next `step`
    // I guess we need a way to pop from `ready_threads` and run it till the next step
}
