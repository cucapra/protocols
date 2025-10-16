use crate::{designs::Design, signal_trace::WaveSignalTrace};

/// The `GlobalContext` stores fields which are common
/// to all threads, such as:
/// - the `WaveSignalTrace` (since all threads are working over the same trace)
/// - the `Design` (since all threads are working over the same `Design`)
/// - other immutable fields
pub struct GlobalContext<'a> {
    /// The waveform supplied by the user
    pub trace: WaveSignalTrace,

    /// The design under test
    pub design: &'a Design,

    /// Whether there are steps remaining in the signal trace
    pub has_steps_remaining: bool,

    /// The `instance_id` corresponding to the DUT instance
    /// (Note: We assume that there is only one `Instance` at the moment)
    pub instance_id: u32,

    /// Indicates whether to print integer literals
    /// using hexadecimal (if `false`, we default to using decimal).
    pub display_hex: bool,
}

impl<'a> GlobalContext<'a> {
    /// Creates a new `GlobalContext` with the provided `trace`,
    /// `design` and `display_hex` flag
    pub fn new(trace: WaveSignalTrace, design: &'a Design, display_hex: bool) -> Self {
        // We assume that there is only one `Instance` at the moment,
        // so we just use the first `PortKey`'s `instance_id`
        let instance_id = trace.port_map.keys().collect::<Vec<_>>()[0].instance_id;

        Self {
            trace,
            design,
            // We haven't run anything yet,
            // so `has_steps_remaining` is initialized to `true`
            has_steps_remaining: true,
            instance_id,
            display_hex,
        }
    }
}
