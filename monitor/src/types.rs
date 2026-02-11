use crate::thread::Thread;

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
#[allow(dead_code)]
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
