// Copyright 2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

/*! Miscellaneous type definitions for the monitor live in this file
 */

use std::{collections::VecDeque, fmt};

use protocols::ir::StmtId;

use crate::{scheduler::Scheduler, thread::Thread};

/// Represents a protocol application like `add(1, 2, 3)` which appears
/// in the protocol trace produced by the monitor.
/// (We can't use the name `Transaction` for this type as it is already
/// used elsewhere in the codebase.)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProtocolApplication {
    pub struct_name: Option<String>,
    pub protocol_name: String,
    pub serialized_args: Vec<String>, // already serialized
}

impl fmt::Display for ProtocolApplication {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref s) = self.struct_name {
            write!(f, "{}::", s)?;
        }
        write!(
            f,
            "{}({})",
            self.protocol_name,
            self.serialized_args.join(", ")
        )
    }
}

/// A `Trace` is just an ordered sequence of `ProtocolApplication`s, e.g.
/// `add(1, 2, 3); add(4, 5, 9), ...]`
pub type Trace = Vec<ProtocolApplication>;

/// An `AugmentedProtocolApplication` represents a singular `ProtocolApplication`
/// (an entry in the the transaction trace produced by the monitor, e.g. `add(1, 2, 3)`)
/// augmented with extra metadata (cycle count, start/end time, thread ID)
#[derive(Clone, Debug)]
pub struct AugmentedProtocolApplication {
    /// The scheduling cycle in which the protocol finished
    pub end_cycle_count: u32,

    /// A concrete protocol with concrete argument values
    pub protocol_application: ProtocolApplication,

    /// The time-step at which the protocol began
    pub start_time_step: u32,

    /// The time-step at which the protocol ended
    pub end_time_step: u32,

    /// The ID of the thread that executed this protocol
    pub thread_id: String,

    /// Whether this transaction was marked `#[idle]` in the protocol file.
    /// Idle entries are excluded from the dedup key but still displayed.
    pub is_idle: bool,
}

/// An `AugmentedTrace` is just a sequence of `AugmentedProtocolApplciation`s,
/// similar to how a `Trace` is just a sequence of `ProtocolApplication`s.
/// (individual protocol calls augmented with extra metatata,
/// e.g. `add(1, 2, 3), add(4, 5, 9), ...`,
/// but with metadata like the Thread ID / start & end time of each protocol).
pub type AugmentedTrace = Vec<AugmentedProtocolApplication>;

/// Conceptually, a `SchedulerGroup` is the collection of
/// all schedulers corresponding to the same `struct` in our DSL,
/// where each scheduler represents a different possible protocol trace.      
/// Practically, a `SchedulerGroup` is implemented as a queue (`VecDeque`)
/// of `Scheduler`s so that we can `push`/`pop` individual `Schedulers`
/// into/from this queue.
pub type SchedulerGroup = VecDeque<Scheduler>;

/// Error types that can occur during scheduler execution
#[derive(Debug)]
pub enum SchedulerError {
    NoTransactionsMatch {
        struct_name: String,
        error_context: anyhow::Error,
    },
    /// Other errors (e.g., internal errors, validation failures)
    Other(anyhow::Error),
}

impl From<anyhow::Error> for SchedulerError {
    fn from(err: anyhow::Error) -> Self {
        SchedulerError::Other(err)
    }
}

/// The result of an individual `Thread`: either it `Completed`,
/// forked explcitly or forked implicitly.
#[derive(Debug)]
pub enum ThreadResult {
    /// Thread completed (moved to next/finished/failed queue)
    Completed,

    /// Thread encountered `fork`. The parent `Thread` is stored as an argument
    /// to this constructor, with the `parent` `Thread`'s state updated to
    /// it's post-`fork` state.
    /// Note: We have to wrap the `Thread` in `Box`, otherwise
    /// Clippy complains that there is a large size difference between different
    /// constructors of this enum.
    ExplicitFork { parent: Box<Thread> },

    /// Thread is laready in the `finished queue and forked implicitly
    /// (e.g. this thread is a protocol which ends with `step` without
    /// ever calling `fork`). The caller of a function which returns
    /// this constructor is responsible for spawning new protocol
    ImplicitFork,
}

/// The result of the *Scheduler* at the end of a cycle
#[derive(Debug)]
pub enum CycleResult {
    Done,
    Fork {
        /// The thread that called fork
        /// (Some for an explicit fork, None for implicit).
        /// Note: We have to wrap the `Thread` in `Box`, otherwise
        /// Clippy complains that there is a large size difference between different
        /// constructors of this enum.
        parent: Box<Option<Thread>>,
    },
}

/// The possible states for an argument to a `repeat` loop.
/// We maintain the following invariants:
/// - `Speculative(n, loopID) `only becomes `Known(n)` after the corresponding
///    scheduler has executed the body of the loop at `loopID` exactly `n`
///    times (note that `n`` can be 0).
/// - Once a `LoopArg` becomes Known, we proceed to the next statement
///   that immediately follows the loop (we don't enter the loop body).
/// - Moreover, once a `LoopArg` remains `Known`, it remains `Known` thereafter.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum LoopArgState {
    /// `Speculative(n, loopID)` means the associated thread has already
    /// *speculatively* executed the loop at `loopID` for `n` iterations.
    /// (The `StmtId` is there to disambiguate between different loop statements,
    /// since different loops can use the same loop argument `n`.)
    Speculative(u64, StmtId),
    Known(u64),
}
