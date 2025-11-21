// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{Instance, designs::Design, global_context::TimeUnit};
use anyhow::Context;
use baa::BitVecValue;
use log::info;
use protocols::ir::SymbolId;
use rustc_hash::FxHashMap;
use wellen::{Hierarchy, SignalRef};

/// The result of advancing the clock cycle by one step
#[derive(Debug)]
pub enum StepResult {
    /// advance time by one step and there are values available for this step
    Ok,
    /// no more values available
    Done,
}

/// Provides a trace of signals that we can analyze.
pub trait SignalTrace {
    /// Advance to the next time step
    /// (This should map 1:1 to a `step` in the Protocol)
    fn step(&mut self) -> StepResult;

    /// Returns value of a design input / output at the current step.
    /// Returns `Err` if the `pin` doesn't exist in the port map
    /// for the given instance.
    fn get(&self, instance_id: u32, pin: SymbolId) -> anyhow::Result<BitVecValue>;
}

/// The `WaveSamplingMode` determines how signals from a waveform are sampled
#[derive(Debug)]
#[allow(dead_code)]
pub enum WaveSamplingMode {
    /// Sample on the rising edge of the signal, specified by its
    /// signal identifier (a `SignalRef`)
    RisingEdge(SignalRef),
    /// Sample on the falling edge of the signal, specified by its
    /// signal identifier (a `SignalRef`)
    FallingEdge(SignalRef),
    /// Interpret every time step as a new clock step. This generally only works
    /// for waveforms produced by the Patronus simulator.
    Direct,
}

/// Waveform dump based implementation of a signal trace.
#[derive(Debug)]
#[allow(dead_code)]
pub struct WaveSignalTrace {
    wave: wellen::simple::Waveform,
    pub port_map: FxHashMap<PortKey, SignalRef>,

    /// The sampling mode to be used on the waveform
    sampling_mode: WaveSamplingMode,

    /// The current (logical) `step()` in the Protocols specification
    logical_step: u32,

    /// The actual clock time-step in the waveform
    time_step: u32,

    /// An (optional) reference to the signal to treat as the clock signal
    /// (to be sampled on every rising clockedge)
    /// Note that this field is only `Some` if the user passes an argument
    /// to the optional `--sample_posedge` CLI argument
    clock_signal: Option<SignalRef>,
}

/// A `PortKey` is just a pair consisting of an `instance_id` and a `symbol_id` for a pin
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PortKey {
    pub instance_id: u32,
    pub pin_id: SymbolId,
}

impl WaveSignalTrace {
    /// Returns the actual clock time-step index in the waveform
    pub fn time_step(&self) -> u32 {
        self.time_step
    }

    /// Returns the actual time value (in the waveform's time units) for a given time_step index
    pub fn time_value(&self, time_step: u32) -> u64 {
        self.wave.time_table()[time_step as usize]
    }

    /// Returns the maximum time value in the waveform (in femtoseconds)
    pub fn max_time(&self) -> u64 {
        if self.wave.time_table().is_empty() {
            return 0;
        }

        let max_time_value = self.wave.time_table()[self.wave.time_table().len() - 1];

        // Convert to femtoseconds based on timescale
        if let Some(timescale) = self.wave.hierarchy().timescale() {
            match timescale.unit {
                wellen::TimescaleUnit::FemtoSeconds => max_time_value,
                wellen::TimescaleUnit::PicoSeconds => max_time_value * 1_000,
                wellen::TimescaleUnit::NanoSeconds => max_time_value * 1_000_000,
                wellen::TimescaleUnit::MicroSeconds => max_time_value * 1_000_000_000,
                wellen::TimescaleUnit::MilliSeconds => max_time_value * 1_000_000_000_000,
                wellen::TimescaleUnit::Seconds => max_time_value * 1_000_000_000_000_000,
                _ => max_time_value,
            }
        } else {
            max_time_value
        }
    }

    /// Formats a time value from the waveform into a human-readable string
    /// using the specified `time_step` (or auto-selecting based on maximum time)
    pub fn format_time(&self, time_step: u32, time_unit: TimeUnit) -> String {
        let time_value = self.time_value(time_step);

        // Convert the time value to femtoseconds (the base unit) using the
        // timescale in the waveform (if one exists)
        let time_fs = if let Some(timescale) = self.wave.hierarchy().timescale() {
            match timescale.unit {
                wellen::TimescaleUnit::FemtoSeconds => time_value,
                wellen::TimescaleUnit::PicoSeconds => time_value * 1_000,
                wellen::TimescaleUnit::NanoSeconds => time_value * 1_000_000,
                wellen::TimescaleUnit::MicroSeconds => time_value * 1_000_000_000,
                wellen::TimescaleUnit::MilliSeconds => time_value * 1_000_000_000_000,
                wellen::TimescaleUnit::Seconds => time_value * 1_000_000_000_000_000,
                _ => time_value,
            }
        } else {
            time_value
        };

        // Format based on the specified unit
        Self::format_time_with_unit(time_fs, time_unit, self.max_time())
    }

    /// Formats a time value using the specified unit (or auto-selecting based on max_time)
    fn format_time_with_unit(
        time_fs: u64,
        time_unit: crate::global_context::TimeUnit,
        max_time_fs: u64,
    ) -> String {
        use crate::global_context::TimeUnit;

        const FS_PER_PS: u64 = 1_000;
        const FS_PER_NS: u64 = 1_000_000;
        const FS_PER_US: u64 = 1_000_000_000;
        const FS_PER_MS: u64 = 1_000_000_000_000;
        const FS_PER_S: u64 = 1_000_000_000_000_000;

        /// Helper function to format a time value with up to `max_decimals`
        /// // decimal places
        fn format_minimal(value: f64, divisor: u64, unit: &str, max_decimals: usize) -> String {
            let scaled = value / divisor as f64;
            // Check whether the scaled time value is a whole number
            if (scaled - scaled.round()).abs() < 1e-10 {
                format!("{}{}", scaled as u64, unit)
            } else {
                // Format with up to max_decimals, removing trailing zeros
                let formatted = format!("{:.prec$}", scaled, prec = max_decimals);
                // Remove trailing zeros and decimal point if not needed
                let trimmed = formatted.trim_end_matches('0').trim_end_matches('.');
                format!("{}{}", trimmed, unit)
            }
        }

        match time_unit {
            TimeUnit::FemtoSeconds => format!("{}fs", time_fs),
            TimeUnit::PicoSeconds => format_minimal(time_fs as f64, FS_PER_PS, "ps", 3),
            TimeUnit::NanoSeconds => format_minimal(time_fs as f64, FS_PER_NS, "ns", 3),
            TimeUnit::MicroSeconds => format_minimal(time_fs as f64, FS_PER_US, "us", 3),
            TimeUnit::MilliSeconds => format_minimal(time_fs as f64, FS_PER_MS, "ms", 6),
            TimeUnit::Seconds => format_minimal(time_fs as f64, FS_PER_S, "s", 6),
            TimeUnit::Auto => {
                // Auto-select based on maximum time
                if max_time_fs >= FS_PER_S {
                    format_minimal(time_fs as f64, FS_PER_S, "s", 6)
                } else if max_time_fs >= FS_PER_MS {
                    format_minimal(time_fs as f64, FS_PER_MS, "ms", 6)
                } else if max_time_fs >= FS_PER_US {
                    format_minimal(time_fs as f64, FS_PER_US, "us", 3)
                } else if max_time_fs >= FS_PER_NS {
                    format_minimal(time_fs as f64, FS_PER_NS, "ns", 3)
                } else if max_time_fs >= FS_PER_PS {
                    format_minimal(time_fs as f64, FS_PER_PS, "ps", 3)
                } else {
                    format!("{}fs", time_fs)
                }
            }
        }
    }

    /// Opens a waveform at the specified `filename` with the given
    /// `Design`s and `Instance`s. The CLI arg `sample_posedge` is passed
    /// as an argument to determine the `WaveSamplingMode` (whether it is
    /// `Direct` or `RisingEdge`).
    pub fn open(
        filename: &impl AsRef<std::path::Path>,
        designs: &FxHashMap<String, Design>,
        instances: &[Instance],
        sample_posedge: Option<String>,
    ) -> Result<Self, wellen::WellenError> {
        let mut wave = wellen::simple::read(filename)?;

        // find instances in the waveform hierarchy
        let (port_map, clock_signal) =
            find_instances(wave.hierarchy(), designs, instances, sample_posedge);

        // Determine the sampling mode based on the vavlue received
        // for `clock_signal`. Note: we only support `Direct` & `RisingEdge`
        // for now (`FallingEdge` is currently unsupported).
        let sampling_mode = if let Some(signal_ref) = clock_signal {
            WaveSamplingMode::RisingEdge(signal_ref)
        } else {
            WaveSamplingMode::Direct
        };

        // load all relavant signal references into memory
        let mut signals: Vec<SignalRef> = port_map.values().cloned().collect();
        // Add clock signal if present
        if let Some(clk_sig) = clock_signal {
            signals.push(clk_sig);
        }
        signals.sort();
        signals.dedup();
        wave.load_signals(&signals);

        Ok(Self {
            wave,
            port_map,
            sampling_mode,

            // At the beginning, zero `step()` calls have happened,
            // so `logical_step` is initialized to 0
            logical_step: 0,

            // The waveform begins with `TimeIdx = 0`
            time_step: 0,

            clock_signal,
        })
    }

    /// Helper function that returns the string representation of a
    /// `SignalValue` associated with a particular `SignalRef`
    /// at a given `time_step`
    fn get_value(&self, signal_ref: SignalRef, time_step: u32) -> String {
        // Get the clock signal
        let signal = self
            .wave
            .get_signal(signal_ref)
            .unwrap_or_else(|| panic!("Unable to get signal for SignalRef {:?}", signal_ref));
        let offset = signal
            .get_offset(time_step)
            .unwrap_or_else(|| panic!("Unable to get offset for time_step {}", time_step));
        // Get the last value in the time step (this is to deal with delta cycles)
        let value = signal.get_value_at(&offset, offset.elements - 1);
        value
            .to_bit_string()
            .unwrap_or_else(|| panic!("Unable to convert {value} to bit-string"))
    }
}

/// Checks instances and returns a pair consisting of the (port map, optional clock signal)
/// (the latter is only `Some` if `sample_posedge` corresponds to a valid signal)
fn find_instances(
    hierachy: &Hierarchy,
    designs: &FxHashMap<String, Design>,
    instances: &[Instance],
    sample_posedge: Option<String>,
) -> (FxHashMap<PortKey, SignalRef>, Option<SignalRef>) {
    let mut port_map = FxHashMap::default();

    let mut clock_signal: Option<SignalRef> = None;

    for (inst_id, inst) in instances.iter().enumerate() {
        // fetch the design from the hashmap (the design tells us what pins to expect)
        let design = &designs[&inst.design_name];

        let inst_name_parts: Vec<&str> = inst.name.split('.').collect();
        if let Some(instance_scope) = hierachy.lookup_scope(&inst_name_parts) {
            let instance_scope = &hierachy[instance_scope];

            // for every pin designed in our struct, we have to find the correct
            // variable that corresponds to it
            for (pin_id, pin) in design.pins.iter() {
                // find a variable that has a matching name
                if let Some(var) = instance_scope
                    .vars(hierachy)
                    .find(|v| hierachy[*v].name(hierachy) == pin.name())
                {
                    let key = PortKey {
                        instance_id: inst_id as u32,
                        pin_id: *pin_id,
                    };
                    let waveform_bits = hierachy[var].length().expect("not a bit vector");

                    // Set up `sample_posedge` to
                    // refer to the clock signal (if one is specified)
                    if let Some(ref signal_name) = sample_posedge {
                        let clock_signal_parts: Vec<&str> = signal_name.split('.').collect();

                        // The clock signal should be in the same scope as the instance
                        // So we look it up directly in the instance_scope
                        match clock_signal_parts.last() {
                            Some(var_name) => {
                                if let Some(var) = instance_scope
                                    .vars(hierachy)
                                    .find(|v| hierachy[*v].name(hierachy) == *var_name)
                                {
                                    let signal_ref = hierachy[var].signal_ref();
                                    clock_signal = Some(signal_ref);
                                } else {
                                    // If not found in instance scope, use `lookup_var`
                                    match hierachy.lookup_var(&clock_signal_parts, var_name) {
                                        Some(var_ref) => {
                                            let signal_ref = hierachy[var_ref].signal_ref();
                                            clock_signal = Some(signal_ref);
                                        }
                                        None => {
                                            panic!("Unable to find signal {var_name} in waveform")
                                        }
                                    }
                                }
                            }
                            None => panic!("Malformed signal {signal_name}"),
                        }
                    }

                    // Check that bit widths match
                    assert_eq!(waveform_bits, pin.bitwidth());

                    // Store the internal Wellen reference to the signal
                    port_map.insert(key, hierachy[var].signal_ref());
                } else {
                    // unable to find a variable whose name matches a pin
                    let available_vars: Vec<&str> = instance_scope
                        .vars(hierachy)
                        .map(|v| hierachy[v].name(hierachy))
                        .collect();
                    panic!(
                        "Failed to find pin {}. Available pins in waveform for instance {} are {}",
                        pin.name(),
                        inst.name,
                        available_vars.join(", ")
                    );
                }
            }
        } else {
            panic!("Failed to find instance {}", inst.name);
        }
    }
    (port_map, clock_signal)
}

impl SignalTrace for WaveSignalTrace {
    /// Advance to the next time step
    /// (This should map 1:1 to a `step` in the Protocol)
    fn step(&mut self) -> StepResult {
        // The no. of times we can call `step` is 1 less than the
        // total no. of cycles available in the signal trace
        let total_steps = (self.wave.time_table().len() - 1) as u32;
        match self.sampling_mode {
            // A `Direct` sampling mode means a `logical_step` maps 1:1
            // to a `time_step` in the waveform
            WaveSamplingMode::Direct => {
                // If we haven't reached the end of the waveform yet
                // (i.e. if `self.logical_step < total_steps`)
                // increment the `logical_step` & `time_step` together
                if self.logical_step < total_steps {
                    self.logical_step += 1;
                    self.time_step += 1;
                }
                if self.logical_step == total_steps {
                    StepResult::Done
                } else {
                    StepResult::Ok
                }
            }
            // Sample on the next rising edge of `clock_signal_ref`
            WaveSamplingMode::RisingEdge(clock_signal_ref) => {
                // First, increment the logical step
                self.logical_step += 1;

                let old_time = self.time_value(self.time_step) / 1_000_000;

                // Next, as long as the time-step is in bounds...
                while self.time_step < total_steps {
                    // ...first fetch the current signal value before incrementing
                    let prev_value = self.get_value(clock_signal_ref, self.time_step);

                    // Then, increment the `time_step`, and check whether
                    // the prevous value is 0 while the new value is 1
                    // If yes, we have encountered a rising clock-edge
                    // and have found the new `time_step` for the waveform
                    self.time_step += 1;
                    let new_value = self.get_value(clock_signal_ref, self.time_step);
                    if prev_value == "0" && new_value == "1" {
                        let new_time = self.time_value(self.time_step) / 1_000_000;

                        info!("Advanced clock time from {old_time}ns -> {new_time}ns");

                        return StepResult::Ok;
                    }
                }
                // If we reach this point, we cannot increment the `time_step`
                // any further, so we return `Done` to indicate that
                // we've reached the end of the waveform
                StepResult::Done
            }
            WaveSamplingMode::FallingEdge(_) => {
                todo!("Handle WaveSamplingMode::FallingEdge when stepping WaveSignalTrace")
            }
        }
    }

    /// Returns value of a design input / output at the current (logical) step.
    /// Returns `Err` if the `pin` doesn't exist in the port map
    /// for the given instance.
    fn get(&self, instance_id: u32, pin: SymbolId) -> anyhow::Result<BitVecValue> {
        let key = PortKey {
            instance_id,
            pin_id: pin,
        };
        // Get the Wellen `SignalRef` (akin to `SignalId`)
        let signal_ref = self
            .port_map
            .get(&key)
            .with_context(|| format!("Key {:?} doesn't exist in port map", key))?;

        // Obtain the `SignalValue` at the current `time_step`
        // (represented as a bit-string)
        let bit_str = self.get_value(*signal_ref, self.time_step);

        Ok(BitVecValue::from_bit_str(&bit_str).unwrap_or_else(|err| {
            panic!(
                "Unable to convert bit-string {bit_str} to BitVecValue, {:?}",
                err
            )
        }))
    }
}
