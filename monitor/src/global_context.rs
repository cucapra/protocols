// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{designs::Design, signal_trace::WaveSignalTrace};

/// The `GlobalContext` stores fields which are common
/// to all threads, such as:
/// - the `WaveSignalTrace` (since all threads are working over the same trace)
/// - the `Design` (since all threads are working over the same `Design`)
/// - other immutable fields
#[derive(Debug)]
pub struct GlobalContext {
    /// The waveform supplied by the user
    pub trace: WaveSignalTrace,

    /// The design under test
    pub design: Design,

    /// The `instance_id` corresponding to the DUT instance
    /// (Note: We assume that there is only one `Instance` at the moment)
    pub instance_id: u32,

    /// Indicates whether to print integer literals
    /// using hexadecimal (if `false`, we default to using decimal).
    pub display_hex: bool,

    /// Indicates whether to display the start & end waveform time for each
    /// inferred transaction
    pub show_waveform_time: bool,
}

impl GlobalContext {
    /// Creates a new `GlobalContext` with the provided `trace`,
    /// `design` and `display_hex` flag. The `display_hex` argument
    /// indicates whether to print integer literals
    /// using hexadecimal (if `false`, we default to using decimal).
    pub fn new(
        trace: WaveSignalTrace,
        design: Design,
        display_hex: bool,
        show_waveform_time: bool,
    ) -> Self {
        // We assume that there is only one `Instance` at the moment,
        // so we just use the first `PortKey`'s `instance_id`
        let instance_id = trace.port_map.keys().collect::<Vec<_>>()[0].instance_id;

        Self {
            trace,
            design,
            instance_id,
            display_hex,
            show_waveform_time,
        }
    }
}
