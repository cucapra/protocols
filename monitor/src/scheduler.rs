// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use protocols::scheduler::Thread;

/// Queue of threads
type Queue<'a> = Vec<Thread<'a>>;

pub struct Scheduler<'a> {
    /// The current queue
    current_queue: Queue<'a>,
    /// The next queue
    next_queue: Queue<'a>,
}
