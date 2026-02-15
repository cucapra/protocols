// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Cli;

/// Time unit for displaying waveform times
#[derive(Debug, Clone, Copy)]
pub enum TimeUnit {
    FemtoSeconds,
    PicoSeconds,
    NanoSeconds,
    MicroSeconds,
    MilliSeconds,
    Seconds,
    Auto, // Auto-select based on the maximum time value
}

impl TimeUnit {
    /// Parses a string into the corresponding `TImeUnit`
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "fs" => Some(TimeUnit::FemtoSeconds),
            "ps" => Some(TimeUnit::PicoSeconds),
            "ns" => Some(TimeUnit::NanoSeconds),
            "us" => Some(TimeUnit::MicroSeconds),
            "ms" => Some(TimeUnit::MilliSeconds),
            "s" => Some(TimeUnit::Seconds),
            "auto" => Some(TimeUnit::Auto),
            _ => None,
        }
    }
}

/// The `GlobalContext` stores fields which are common
/// to all threads, e.g.:
/// - the `Design` (since all threads are working over the same `Design`)
/// - other immutable fields (configuration flags)
///   Note: The `WaveSignalTrace` is owned by `GlobalScheduler` and passed
///   as needed
#[derive(Debug)]
pub struct GlobalContext {
    /// The name of the waveform file supplied by the user
    /// (Only used for error-reporting purposes)
    pub waveform_file: String,

    /// The `instance_id` corresponding to the DUT instance
    pub instance_id: u32,

    /// Indicates whether to print integer literals
    /// using hexadecimal (if `false`, we default to using decimal).
    pub display_hex: bool,

    /// Indicates whether to display the start & end waveform time for each
    /// inferred transaction
    pub show_waveform_time: bool,

    /// The time unit to use for displaying waveform times
    pub time_unit: TimeUnit,

    /// Indicates whether to print the no. of logical steps (i.e. clock cycles)
    /// taken by the monitor
    pub print_num_steps: bool,

    /// Indicates if there are multiple (more than 1) structs in the source file
    pub multiple_structs: bool,

    /// Indicates whether to print out thread IDs for each inferred transaction
    pub show_thread_ids: bool,
}

impl GlobalContext {
    /// Creates a new `GlobalContext` with the provided `design`
    /// and configuration flags as specified by the user via the `Cli`.
    /// The `display_hex` field indicates whether to print integer literals
    /// in hexadecimal (if `false`, we default to using decimal).
    /// Note: this function is meant to be called from `main.rs` only
    /// upon monitor initialization.
    pub fn new(cli: &Cli, instance_id: u32, time_unit: TimeUnit, multiple_structs: bool) -> Self {
        Self {
            waveform_file: cli.wave.clone(),
            instance_id,
            display_hex: cli.display_hex,
            show_waveform_time: cli.show_waveform_time,
            time_unit,
            print_num_steps: cli.print_num_steps,
            multiple_structs,
            show_thread_ids: cli.show_thread_ids,
        }
    }
}
