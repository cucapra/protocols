// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{designs::Design, Instance};
use anyhow::Context;
use baa::BitVecValue;
use protocols::ir::SymbolId;
use rustc_hash::FxHashMap;
use wellen::{Hierarchy, SignalRef};

// TODO: add an extra (optional) CLI flag for the monitor
// `--sample_posedge = clk`
// which tells the monitor which signal to treat as the clock and to sample on
// every rising edge

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

    /// returns value of a design input / output at the current step
    fn get(&self, instance_id: u32, io: SymbolId) -> anyhow::Result<BitVecValue>;
}

/// Determines how signals from a waveform a sampled
/// TODO: change the arg of RisingEdge to a SignalRef
#[derive(Debug)]
#[allow(dead_code)]
pub enum WaveSamplingMode<'a> {
    /// sample on the rising edge of the signal specified by its hierarchical name
    RisingEdge(&'a str),
    /// sample on the falling edge of the signal specified by its hierarchical name
    FallingEdge(&'a str),
    /// Interpret every time step as a new clock step. This generally only works for waveforms
    /// produced by the patronus simulator.
    Direct,
}

/// Waveform dump based implementation of a signal trace.
#[derive(Debug)]
#[allow(dead_code)]
pub struct WaveSignalTrace {
    wave: wellen::simple::Waveform,
    pub port_map: FxHashMap<PortKey, SignalRef>,

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
    pub fn open(
        filename: &impl AsRef<std::path::Path>,
        mode: WaveSamplingMode,
        designs: &FxHashMap<String, Design>,
        instances: &[Instance],
        sample_posedge: Option<String>,
    ) -> Result<Self, wellen::WellenError> {
        match mode {
            WaveSamplingMode::Direct => {} // ok
            m => todo!("Unsupported sampling mode: {m:?}"),
        }
        let mut wave = wellen::simple::read(filename)?;

        // find instances in the waveform hierarchy
        let (port_map, clock_signal) =
            find_instances(wave.hierarchy(), designs, instances, sample_posedge);

        // load all relavant signal references into memory
        let mut signals: Vec<SignalRef> = port_map.values().cloned().collect();
        signals.sort();
        signals.dedup();
        wave.load_signals(&signals);

        Ok(Self {
            wave,
            port_map,

            // At the beginning, zero `step()` calls have happened,
            // so `logical_step` is initialized to 0
            logical_step: 0,

            // The waveform begins with `TimeIdx = 0`
            time_step: 0,

            clock_signal,
        })
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

                    // TODO: figure out how to set up `sample_posedge` to
                    // refer to the clock signal (if one is specified)

                    match sample_posedge {
                        Some(ref signal_name) => {
                            let clock_signal_parts: Vec<&str> = signal_name.split('.').collect();
                            match clock_signal_parts.last() {
                                Some(signal_name) => {
                                    match hierachy.lookup_var(&clock_signal_parts, signal_name) {
                                        Some(var_ref) => {
                                            let signal_ref = hierachy[var_ref].signal_ref();
                                            clock_signal = Some(signal_ref);
                                        }
                                        None => panic!(
                                            "Unable to find signal {signal_name} in waveform"
                                        ),
                                    }
                                }
                                None => panic!("Malformed signal {signal_name}"),
                            }
                        }
                        None => (),
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
        if self.logical_step < total_steps {
            self.logical_step += 1;
        }
        if self.logical_step == total_steps {
            StepResult::Done
        } else {
            StepResult::Ok
        }
    }

    /// Returns value of a design input / output at the current (logical) step
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
