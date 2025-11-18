// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{designs::Design, Instance};
use anyhow::Context;
use baa::BitVecValue;
use protocols::ir::SymbolId;
use rustc_hash::FxHashMap;
use wellen::{Hierarchy, Signal, SignalRef};

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

    fn get_value(&self, signal: &Signal, time_step: u32) -> String {
        let offset = signal
            .get_offset(time_step)
            .unwrap_or_else(|| panic!("Unable to get offset for time_step {}", time_step));
        // get the last value in the time step (this is to deal with delta cycles)
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
                        match clock_signal_parts.last() {
                            Some(signal_name) => {
                                match hierachy.lookup_var(&clock_signal_parts, signal_name) {
                                    Some(var_ref) => {
                                        let signal_ref = hierachy[var_ref].signal_ref();
                                        clock_signal = Some(signal_ref);
                                    }
                                    None => {
                                        panic!("Unable to find signal {signal_name} in waveform")
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
    /// TODO: pattern-match on the `SamplingMode`
    /// - keep the existing logic for `SamplingMode::Direct`
    /// - If `RisingEdge`, increment the logic step and find out the correct `time_step` to go to
    /// - Don't need to handle `FallingEdge` for now
    fn step(&mut self) -> StepResult {
        // The no. of times we can call `step` is 1 less than the
        // total no. of cycles available in the signal trace
        let total_steps = (self.wave.time_table().len() - 1) as u32;
        match self.sampling_mode {
            // A `Direct` sampling mode means a `logical_step` maps 1:1
            // to a `time_step` in the waveform
            WaveSamplingMode::Direct => {
                if self.logical_step < total_steps {
                    self.logical_step += 1;
                }
                if self.logical_step == total_steps {
                    StepResult::Done
                } else {
                    StepResult::Ok
                }
            }
            WaveSamplingMode::RisingEdge(clock_signal_ref) => {
                // Increment the logical step
                self.logical_step += 1;

                // Get the clock signal
                let signal = self.wave.get_signal(clock_signal_ref).unwrap_or_else(|| {
                    panic!("Unable to get signal for SignalRef {:?}", clock_signal_ref)
                });

                // Find the current signal value
                let prev_value = self.get_value(signal, self.time_step);

                // As long as the time-step is in bounds...
                while self.time_step < total_steps {
                    // Increment the `time_step`, and check whether
                    // the prevous value is 0 while the new value is 1
                    // If yes, we have encountered a rising clock-edge
                    // and hvae found the new `time_step` for the waveform
                    self.time_step += 1;
                    let new_value = self.get_value(signal, self.time_step);
                    if prev_value == "0" && new_value == "1" {
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
        // Get the actual `Signal`
        let signal = self
            .wave
            .get_signal(*signal_ref)
            .with_context(|| format!("Unable to get signal for pin_id {pin}"))?;
        // Currently, this finds the closest `TimeIdx` that is <= to the desired (clock) time
        let offset = signal
            .get_offset(self.time_step)
            .with_context(|| format!("Unable to get offset for time_step {}", self.time_step))?;
        // get the last value in the time step (this is to deal with delta cycles)
        let value = signal.get_value_at(&offset, offset.elements - 1);
        let bit_str = value
            .to_bit_string()
            .with_context(|| format!("Unable to convert {value} to bit-string"))?;
        Ok(BitVecValue::from_bit_str(&bit_str).unwrap_or_else(|err| {
            panic!(
                "Unable to convert bit-string {bit_str} to BitVecValue, {:?}",
                err
            )
        }))
    }
}
