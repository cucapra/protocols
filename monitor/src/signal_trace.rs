// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Design, Instance};
use baa::BitVecValue;
use protocols::ir::SymbolId;
use rustc_hash::FxHashMap;
use wellen::{Hierarchy, SignalRef};

#[allow(dead_code)]
pub enum StepResult {
    /// advance time by one step and there are values available for this step
    Ok,
    /// no more values available
    Done,
}

/// Provides a trace of signals that we can analyze.
#[allow(dead_code)]
pub trait SignalTrace {
    /// advance to the next time step
    fn step() -> StepResult;

    /// returns value of a design input / output at the current step
    fn get(instance_id: u32, io: SymbolId) -> BitVecValue;
}

/// Determines how signals from a waveform a sampled
#[allow(dead_code)]
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
#[allow(dead_code)]
pub struct WaveSignalTrace {
    wave: wellen::simple::Waveform,
    port_map: FxHashMap<PortKey, SignalRef>,
}

/// A PortKey is just a pair consisting of an instance_id and a symbol_id for a pin
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

        // load all relavant signal references into memory
        let mut signals: Vec<_> = port_map.values().cloned().collect();
        signals.sort();
        signals.dedup();
        wave.load_signals(&signals);

        Ok(Self { wave, port_map })
    }
}

/// check instances and build port map
#[allow(unused_variables)]
fn find_instances(
    h: &Hierarchy,
    designs: &FxHashMap<String, Design>,
    instances: &[Instance],
) -> FxHashMap<PortKey, SignalRef> {
    let mut port_map = FxHashMap::default();
    for (inst_id, inst) in instances.iter().enumerate() {
        // fetch the design from the hashmap (the design tells us what pins to expect)
        let design = &designs[&inst.design];

        let inst_name_parts: Vec<_> = inst.name.split('.').collect();
        if let Some(instance_scope) = h.lookup_scope(&inst_name_parts) {
            let instance_scope = &h[instance_scope];

            // for every pin designed in our struct, we have to find the correct
            // variable that corresponds to it
            for pin in design.pins.iter() {
                // find a variable that has a matching name
                if let Some(var) = instance_scope.vars(h).find(|v| h[*v].name(h) == pin.name()) {
                    // TODO: how do we get the correct "pin" id here? (Look at the Protocols IR)
                    // (i.e. `pin` here should not be default, it should be the `SymbolId`)
                    // Note: the key here is not fully correct as a result
                    let key = PortKey {
                        instance_id: inst_id as u32,
                        pin: Default::default(),
                    };
                    let waveform_bits = h[var].length().expect("not a bit vector");

                    // TODO: check that bit widths match
                    // assert_eq!(waveform_bits, pin.tpe().);

                    // Store the internal Wellen reference to the signal
                    port_map.insert(key, h[var].signal_ref());
                } else {
                    // unable to find a variable whose name matches a pin
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

    fn get(_instance_id: u32, _pin: SymbolId) -> BitVecValue {
        todo!()
    }
}

// Concrete TODOs:
// - Find the concrete symbol ID for `DUT.a`
// ^^ this may necessitate refactoring the IR

// - Look at how languages with symbol tables (e.g. Rust) compiles records
// - Idea; Build a format string: `<name_of_design>.<name_of_pin>`
// ^^ use that to index into the symbol table
