// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use crate::thread::Thread;

/// Queue of threads
type Queue = Vec<Thread>;

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
}
