// Copyright 2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

/*! This file defines a `Queue` data structure, representing a ready
 *  queue of threads. This type is used in the monitor scheduler.
 */

use std::collections::VecDeque;

use protocols::serialize::serialize_stmt;

use crate::{global_context::GlobalContext, signal_trace::WaveSignalTrace, thread::Thread};

/// `Queue` is just a type alias for `VecDeque<Thread>`.
/// We use a `VecDeque` instead of `Vec`, since `VecDeque::pop_back` produces
/// elements in a FIFO order (which is what we want),
/// whereas `Vec::pop` returns elements in LIFO order
pub type Queue = VecDeque<Thread>;

/// Formats a queue's contents into a pretty-printed string
/// Note: we can't implement the `Display` trait for `Queue` since
/// `Queue` is just a type alias
pub fn format_queue(
    queue: &Queue,
    ctx: &GlobalContext,
    trace: &WaveSignalTrace,
    struct_name: &str,
) -> String {
    if !queue.is_empty() {
        let formatted_queue = queue
            .iter()
            .map(|thread| format_thread(thread, ctx, trace, struct_name))
            .collect::<Vec<String>>()
            .join("\n\t");
        format!("\n\t{}", formatted_queue)
    } else {
        "<EMPTY>".to_string()
    }
}

/// Formats a single thread with context-aware timing information
pub fn format_thread(
    thread: &Thread,
    ctx: &GlobalContext,
    trace: &WaveSignalTrace,
    struct_name: &str,
) -> String {
    let start_info = if ctx.show_waveform_time {
        format!(
            "Start time: {}",
            trace.format_time(thread.start_time_step, ctx.time_unit)
        )
    } else {
        format!("Start cycle: {}", thread.start_cycle)
    };

    let transaction_name = if ctx.multiple_structs {
        format!("{}::{}", struct_name, thread.transaction.name)
    } else {
        thread.transaction.name.clone()
    };

    format!(
        "THREAD {}: {{ {}, Transaction: `{}`, Current stmt: `{}` ({}) }}",
        thread.global_thread_id(ctx),
        start_info,
        transaction_name,
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
pub fn format_queue_compact(queue: &Queue, ctx: &GlobalContext) -> String {
    if !queue.is_empty() {
        queue
            .iter()
            .map(|thread| {
                format!(
                    "Thread {} (`{}`)",
                    thread.global_thread_id(ctx),
                    thread.transaction.name
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
