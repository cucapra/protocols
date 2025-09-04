// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Design, Instance};
use baa::BitVecValue;
use protocols::ir::{SymbolId, SymbolTable};
use protocols::parser::Rule::assert_eq;
use rustc_hash::FxHashMap;
use std::ptr::write_volatile;
use wellen::{Hierarchy, SignalRef};

pub enum StepResult {
    /// advance time by one step and there are values available for this step
    Ok,
    /// no more values available
    Done,
}

/// Provides a trace of signals that we can analyze.
pub trait SignalTrace {
    /// advance to the next time step
    fn step() -> StepResult;

    /// returns value of a design input / output at the current step
    fn get(instance_id: u32, io: SymbolId) -> BitVecValue;
}

/// Determines how signals from a waveform a sampled
#[derive(Debug)]
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
pub struct WaveSignalTrace {
    wave: wellen::simple::Waveform,
    port_map: FxHashMap<PortKey, SignalRef>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct PortKey {
    instance_id: u32,
    pin: SymbolId,
}

impl WaveSignalTrace {
    pub fn open(
        filename: &impl AsRef<std::path::Path>,
        mode: WaveSamplingMode,
        designs: &FxHashMap<String, Design>,
        instances: &[Instance],
    ) -> Result<Self, wellen::WellenError> {
        match mode {
            WaveSamplingMode::Direct => {} // ok
            m => todo!("Unsupported sampling mode: {m:?}"),
        }
        let mut wave = wellen::simple::read(filename)?;

        // find instances in the waveform hierarchy
        let port_map = find_instances(wave.hierarchy(), designs, instances);

        // load all relavant signals into memory
        let mut signals: Vec<_> = port_map.values().cloned().collect();
        signals.sort();
        signals.dedup();
        wave.load_signals(&signals);

        Ok(Self { wave, port_map })
    }
}

/// check instances and build port map
fn find_instances(
    h: &Hierarchy,
    designs: &FxHashMap<String, Design>,
    instances: &[Instance],
) -> FxHashMap<PortKey, SignalRef> {
    let mut port_map = FxHashMap::default();
    for (inst_id, inst) in instances.iter().enumerate() {
        let design = &designs[&inst.design];

        let inst_name_parts: Vec<_> = inst.name.split('.').collect();
        if let Some(instance_scope) = h.lookup_scope(&inst_name_parts) {
            let instance_scope = &h[instance_scope];
            for pin in design.pins.iter() {
                if let Some(var) = instance_scope.vars(h).find(|v| h[*v].name(h) == pin.name()) {
                    // TODO: how do we get the correct "pin" id here? by position?
                    let key = PortKey {
                        instance_id: inst_id as u32,
                        pin: Default::default(),
                    };
                    let waveform_bits = h[var].length().expect("not a bit vector");
                    // TODO: check that bit widths match
                    // assert_eq!(waveform_bits, pin.tpe().);
                    port_map.insert(key, h[var].signal_ref());
                } else {
                    let available_vars: Vec<_> =
                        instance_scope.vars(h).map(|v| h[v].name(h)).collect();
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
    port_map
}

impl SignalTrace for WaveSignalTrace {
    fn step() -> StepResult {
        todo!()
    }

    fn get(instance_id: u32, pin: SymbolId) -> BitVecValue {
        todo!()
    }
}
