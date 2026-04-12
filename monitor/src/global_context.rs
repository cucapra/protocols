// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Cli;

/// The `GlobalContext` stores fields which are common to all scheduler groups
/// (regardless of which `struct` they belong to), such as CLI configuration
/// flags.
/// Note: The `WaveSignalTrace` is owned by `GlobalScheduler` and passed
/// as needed.
#[derive(Clone)]
pub struct GlobalContext {
    /// The name of the waveform file supplied by the user
    /// (Only used for error-reporting purposes)
    pub waveform_file: String,

    /// Indicates whether to print integer literals
    /// using hexadecimal (if `false`, we default to using decimal).
    pub display_hex: bool,

    /// Indicates whether to display the start & end waveform time for each
    /// inferred transaction
    pub show_waveform_time: bool,

    /// Indicates whether to print the no. of logical steps (i.e. clock cycles)
    /// taken by the monitor
    pub print_num_steps: bool,

    /// Indicates if there are multiple (more than 1) structs in the source file
    pub multiple_structs: bool,

    /// Indicates whether to print out thread IDs for each inferred transaction
    pub show_thread_ids: bool,

    /// Indicates whether to print out `idle` transactions (regardless of
    /// whether they've been annotated with `#[idle]`)
    pub include_idle: bool,

    /// If `Some(n)`, the monitor stops after processing `n` clock cycles.
    /// Useful for quickly testing a protocol against the beginning of a
    /// large waveform without waiting for the full trace to be processed.
    pub max_steps: Option<u32>,
}

impl GlobalContext {
    /// Creates a new `GlobalContext` with
    /// the configuration flags as specified by the user via the `Cli`.
    /// The `display_hex` field indicates whether to print integer literals
    /// in hexadecimal (if `false`, we default to using decimal).
    /// Note: this function is meant to be called from `main.rs` only
    /// upon monitor initialization.
    pub fn new(cli: &Cli, multiple_structs: bool) -> Self {
        Self {
            waveform_file: cli.wave.clone(),
            display_hex: cli.display_hex,
            show_waveform_time: cli.show_waveform_time,
            print_num_steps: cli.print_num_steps,
            multiple_structs,
            show_thread_ids: cli.show_thread_ids,
            include_idle: cli.include_idle,
            max_steps: cli.max_steps,
        }
    }
}
