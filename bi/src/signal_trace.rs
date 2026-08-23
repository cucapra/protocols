// Copyright 2025-26 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Instance;
use baa::{BitVecMutOps, BitVecOps, BitVecValue, BitVecValueRef, WidthInt};
use protocols::frontend::Module;
use protocols::frontend::symbol::SymbolId;
use rand::{Rng, SeedableRng};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::io::BufReader;
use wellen::stream::StreamError;
use wellen::{Hierarchy, SignalRef, SignalValueRef, Time, Timescale, TimescaleUnit};

/// Handle to all signal values at a point in time.
/// Used in `stream_time_steps`.
#[derive(Debug, Clone)]
pub struct SignalValues<'a> {
    port_map: &'a FxHashMap<PortKey, usize>,
    values: &'a [BitVecValue],
}

impl<'a> SignalValues<'a> {
    /// Returns value of a design input / output at the current step.
    pub fn get(&self, instance_id: u32, pin_id: SymbolId) -> BitVecValueRef<'_> {
        let key = PortKey {
            instance_id,
            pin_id,
        };
        let index = self.port_map[&key];
        (&self.values[index]).into()
    }
}

/// Provides a trace of signals that we can analyze.
pub trait SignalTrace {
    /// Streams time steps.
    fn stream_steps(&mut self, callback: impl FnMut(u32, SignalValues)) -> Result<(), String>;

    fn step_to_time(&self) -> StepToTime;
}

/// The `WaveSamplingMode` determines how signals from a waveform are sampled
#[derive(Debug, Clone)]
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
    wave: wellen::stream::StreamingWaveform<BufReader<std::fs::File>>,
    port_map: FxHashMap<PortKey, usize>,
    signal_ref_to_idx: FxHashMap<SignalRef, usize>,
    /// signals to stream
    signals: Vec<SignalRef>,

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

    /// Maps a logical step to time.
    logical_step_to_time: Vec<Time>,
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
        modules: &[Module],
        instances: &[Instance],
        sample_posedge: Option<String>,
    ) -> Result<Self, wellen::WellenError> {
        let opts = wellen::LoadOptions::default();
        let wave = wellen::stream::read_from_file(filename, &opts)?;

        // find instances in the waveform hierarchy
        let (port_to_signal, clock_signal) =
            find_instances(wave.hierarchy(), modules, instances, sample_posedge);

        // Determine the sampling mode based on the vavlue received
        // for `clock_signal`. Note: we only support `Direct` & `RisingEdge`
        // for now (`FallingEdge` is currently unsupported).
        let sampling_mode = if let Some(signal_ref) = clock_signal {
            WaveSamplingMode::RisingEdge(signal_ref)
        } else {
            WaveSamplingMode::Direct
        };

        // load all relavant signal references into memory
        let mut signals: Vec<SignalRef> = port_to_signal.values().cloned().collect();
        // Add clock signal if present
        if let Some(clk_sig) = clock_signal {
            signals.push(clk_sig);
        }
        signals.sort();
        signals.dedup();

        let signal_ref_to_idx: FxHashMap<SignalRef, usize> = signals
            .iter()
            .cloned()
            .enumerate()
            .map(|(ii, s)| (s, ii))
            .collect();
        let port_map = port_to_signal
            .iter()
            .map(|(p, s)| (*p, signal_ref_to_idx[s]))
            .collect();

        Ok(Self {
            wave,
            port_map,
            signal_ref_to_idx,
            signals,
            sampling_mode,
            logical_step: 0,
            time_step: 0,
            clock_signal,
            logical_step_to_time: vec![],
        })
    }
}

/// Checks instances and returns a pair consisting of the (port map, optional clock signal)
/// (the latter is only `Some` if `sample_posedge` corresponds to a valid signal)
fn find_instances(
    hierachy: &Hierarchy,
    modules: &[Module],
    instances: &[Instance],
    sample_posedge: Option<String>,
) -> (FxHashMap<PortKey, SignalRef>, Option<SignalRef>) {
    let mut port_map = FxHashMap::default();

    let mut clock_signal: Option<SignalRef> = None;

    for (inst_id, inst) in instances.iter().enumerate() {
        let module = &modules[inst.module_id];

        let inst_name_parts: Vec<&str> = inst.name.split('.').collect();
        if let Some(instance_scope) = hierachy.lookup_scope(&inst_name_parts) {
            let instance_scope = &hierachy[instance_scope];

            // for every pin designed in our struct, we have to find the correct
            // variable that corresponds to it
            for (field_idx, field) in module.pins.iter().enumerate() {
                let pin_name = field.name().to_string();
                // find a variable that has a matching name
                if let Some(var) = instance_scope
                    .vars(hierachy)
                    .find(|v| hierachy[*v].name(hierachy) == pin_name)
                {
                    let waveform_bits = hierachy[var].length(hierachy).expect("not a bit vector");

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
                                    match hierachy.lookup_var(
                                        &clock_signal_parts[0..clock_signal_parts.len() - 1],
                                        var_name,
                                    ) {
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
                    assert_eq!(
                        waveform_bits,
                        field.bitwidth(),
                        "The bit-width of the waveform value is {}, which doesn't match expected width of {}, which is {}",
                        waveform_bits,
                        pin_name,
                        field.bitwidth()
                    );

                    // store a mapping from any SymbolId that refers to this pin
                    let value = hierachy[var].signal_ref();
                    for syms in &module.proto_pin_map {
                        let key = PortKey {
                            instance_id: inst_id as u32,
                            pin_id: syms[field_idx],
                        };
                        port_map.insert(key, value);
                    }
                } else {
                    // unable to find a variable whose name matches a pin
                    let available_vars: Vec<&str> = instance_scope
                        .vars(hierachy)
                        .map(|v| hierachy[v].name(hierachy))
                        .collect();
                    panic!(
                        "Failed to find pin {}. Available pins in waveform for instance {} are {}",
                        field.name(),
                        inst.name,
                        available_vars.join(",\n")
                    );
                }
            }
        } else {
            panic!(
                "Failed to find instance {}. First scope: {:#?}",
                inst.name,
                hierachy.first_scope().unwrap().full_name(hierachy)
            );
        }
    }
    (port_map, clock_signal)
}

impl SignalTrace for WaveSignalTrace {
    fn stream_steps(&mut self, mut callback: impl FnMut(u32, SignalValues)) -> Result<(), String> {
        let signals = self.signals.clone();
        // random initial values
        let mut rng = RefCell::new(rand::rngs::SmallRng::seed_from_u64(0));
        let mut bv_values: Vec<_> = signals
            .iter()
            .map(|s| {
                let width = self
                    .wave
                    .hierarchy()
                    .get_signal_tpe(*s)
                    .unwrap()
                    .length()
                    .unwrap();
                BitVecValue::random(rng.get_mut(), width)
            })
            .collect();
        let mut times = vec![];
        let filter = wellen::stream::Filter::include_signals(&signals);
        let sampling_mode = self.sampling_mode.clone();
        let mut step_id = 0;
        let mut prev_clock = false;
        self.wave
            .stream_time_steps::<()>(filter, |time, values, changed| {
                let is_step = match sampling_mode {
                    WaveSamplingMode::RisingEdge(clock) => {
                        let current_clock: bool = values.get(&clock).unwrap().try_into().unwrap();
                        let is_step = !prev_clock && current_clock;
                        prev_clock = current_clock;
                        is_step
                    }
                    WaveSamplingMode::FallingEdge(_) => todo!(),
                    WaveSamplingMode::Direct => true,
                };
                if is_step {
                    for s in changed {
                        let idx = self.signal_ref_to_idx[s];
                        let value_ref = values.get(s).unwrap();
                        if let SignalValueRef::BitVec(value) = value_ref {
                            bv_values[idx].assign_from_bytes_be(value.be_bytes().unwrap());
                        } else {
                            unreachable!("we only expect bit vectors");
                        }
                    }
                    times.push(time);
                    callback(
                        step_id,
                        SignalValues {
                            port_map: &self.port_map,
                            values: &bv_values,
                        },
                    );
                    step_id += 1;
                }
                Ok(())
            })
            .map_err(|e| match e {
                StreamError::Wellen(e) => e.to_string(),
                StreamError::Callback(_) => "???".to_string(),
            })?;
        self.logical_step_to_time = times;

        Ok(())
    }

    fn step_to_time(&self) -> StepToTime {
        StepToTime {
            logical_step_to_time: self.logical_step_to_time.clone(),
            timescale: self.wave.hierarchy().timescale(),
        }
    }
}

pub struct StepToTime {
    logical_step_to_time: Vec<wellen::Time>,
    timescale: Option<Timescale>,
}

impl StepToTime {
    pub fn step_to_ns(&self, logical_step: u32) -> String {
        let time = *self
            .logical_step_to_time
            .get(logical_step as usize)
            .unwrap_or_else(|| self.logical_step_to_time.last().unwrap());
        if let Some(timescale) = self.timescale.as_ref() {
            let time = time * timescale.factor as u64;
            match timescale.unit {
                TimescaleUnit::FemtoSeconds => format!("{}ns", time as f64 / 1000.0 / 1000.0),
                TimescaleUnit::PicoSeconds => format!("{}ns", time as f64 / 1000.0),
                TimescaleUnit::NanoSeconds => format!("{}ns", time),
                TimescaleUnit::MicroSeconds => format!("{}ns", time as f64 * 1000.0),
                TimescaleUnit::MilliSeconds => format!("{}ns", time as f64 * 1000.0 * 1000.0),
                TimescaleUnit::Seconds => format!("{}ns", time as f64 * 1000.0 * 1000.0 * 1000.0),
                other => todo!("support {other:?}"),
            }
        } else {
            format!("{}ns", time)
        }
    }
}

/// for our custom ASCI based wave trace format
pub struct AsciWaveTrace {
    // pin id -> step
    values: Vec<Vec<BitVecValue>>,
    pins: Vec<(String, WidthInt)>,
    port_map: FxHashMap<PortKey, usize>,
}

impl AsciWaveTrace {
    pub fn open(
        filename: impl AsRef<std::path::Path>,
        modules: &[Module],
        instances: &[Instance],
    ) -> std::io::Result<Self> {
        let mut rnd = rand::rngs::SmallRng::seed_from_u64(0);
        let content = std::fs::read_to_string(filename)?;
        let mut trace = Self::parse(&content, &mut rnd);

        // populate pin map
        for (inst_id, inst) in instances.iter().enumerate() {
            let module = &modules[inst.module_id];
            for (field_idx, field) in module.pins.iter().enumerate() {
                let pin_name = field.name().to_string();
                let name = if inst.name.is_empty() {
                    pin_name
                } else {
                    format!("{}.{}", inst.name, pin_name)
                };

                if let Some(wave_id) = trace.pins.iter().position(|(n, _)| n == &name) {
                    assert_eq!(
                        trace.pins[wave_id].1,
                        field.bitwidth(),
                        "Width missmatch for {name}"
                    );

                    // store a mapping from any SymbolId that refers to this pin
                    for syms in &module.proto_pin_map {
                        let key = PortKey {
                            instance_id: inst_id as u32,
                            pin_id: syms[field_idx],
                        };
                        trace.port_map.insert(key, wave_id);
                    }
                } else {
                    panic!("Unable to find pin {name}");
                }
            }
        }

        Ok(trace)
    }

    pub fn parse(content: &str, rnd: &mut impl Rng) -> Self {
        let mut out = Self {
            values: vec![],
            pins: vec![],
            port_map: Default::default(),
        };

        let mut pin_ids: FxHashMap<String, usize> = FxHashMap::default();

        for mut line in content.lines() {
            // strip comments
            if let Some(pos) = line.find("//") {
                line = &line[0..pos];
            }
            // strip whitespace
            line = line.trim();
            if line.is_empty() {
                continue;
            }
            // parse signal
            let (name, width, mut values) = parse_signal_line(line, rnd);
            if let Some(existing_id) = pin_ids.get(&name) {
                out.values[*existing_id].append(&mut values);
            } else {
                pin_ids.insert(name.clone(), out.pins.len());
                out.values.push(values);
                out.pins.push((name, width));
            }
        }

        debug_assert_eq!(out.pins.len(), out.values.len());
        if !out.pins.is_empty() {
            let num_steps = out.values[0].len();
            assert!(
                out.values.iter().all(|v| v.len() == num_steps),
                "different pins have a different number of signal values!\n{:?}",
                out.pins
                    .iter()
                    .zip(out.values.iter().map(|v| v.len()))
                    .map(|((name, _), l)| format!("{name}: {l}"))
                    .collect::<Vec<_>>()
            );
        }

        out
    }
}

fn parse_signal_line(line: &str, rnd: &mut impl Rng) -> (String, WidthInt, Vec<BitVecValue>) {
    let tokens = tokenize(line);
    assert!(!tokens.is_empty());
    let (name, width) = parse_name_and_width(tokens[0]);
    let values = tokens
        .into_iter()
        .skip(1)
        .map(|t| parse_value(t, width, rnd))
        .collect();
    (name, width, values)
}

fn parse_name_and_width(value: &str) -> (String, WidthInt) {
    if let Some(start) = value.find('[') {
        let col_pos = value.find(':').expect("missing `:`");
        assert!(col_pos > start);
        let msb: WidthInt = value[start + 1..col_pos]
            .parse()
            .expect("failed to parse MSB");
        let end = value.find(']').expect("missing `]`");
        assert!(end > col_pos);
        let lsb: WidthInt = value[col_pos + 1..end]
            .parse()
            .expect("failed to parse LSB");
        assert!(msb >= lsb);
        let width = msb - lsb + 1;
        let name = value[0..start].to_string();
        (name, width)
    } else {
        (value.to_string(), 1)
    }
}

fn parse_value(value: &str, width: WidthInt, rnd: &mut impl rand::Rng) -> BitVecValue {
    let value = value.to_lowercase();
    let r = if value == "x" {
        BitVecValue::random(rnd, width)
    } else if let Some(v) = value.strip_prefix("0x") {
        BitVecValue::from_hex_str(v).unwrap()
    } else if let Some(v) = value.strip_prefix("0b") {
        BitVecValue::from_bit_str(v).unwrap()
    } else {
        BitVecValue::from_str_radix(&value, 10, width).unwrap()
    };
    if r.width() < width {
        r.zero_extend(width - r.width())
    } else {
        r
    }
}

fn tokenize(line: &str) -> Vec<&str> {
    line.split(|c: char| c.is_whitespace())
        .filter(|e| !e.is_empty())
        .collect()
}

impl SignalTrace for AsciWaveTrace {
    fn stream_steps(&mut self, mut callback: impl FnMut(u32, SignalValues)) -> Result<(), String> {
        let num_steps = self.values[0].len();
        debug_assert!(self.values.iter().all(|v| v.len() == num_steps));
        for step in 0..num_steps {
            let bv_values: Vec<_> = self.values.iter().map(|v| v[step].clone()).collect();
            callback(
                step as u32,
                SignalValues {
                    port_map: &self.port_map,
                    values: &bv_values,
                },
            );
        }
        Ok(())
    }

    fn step_to_time(&self) -> StepToTime {
        let num_steps = self.values[0].len() as Time;
        StepToTime {
            logical_step_to_time: (0..num_steps).collect(),
            timescale: None,
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_asci_trace() {
        let content = r#"
// https://cdn.opencores.org/downloads/wbspec_b4.pdf
// Illustration 3-5
ADR_O[31:0]  X 0x1234  0x1234 X
DAT_I[31:0]  X      X  0xffff X
DAT_O[31:0]  X      X       X X
WE_O         0      0       0 0
SEL_O[3:0]   X    0xf     0xf X
STB_O        0      1       1 0
ACK_I        0      0       1 0
CYC_O        0      1       1 0
// we ignore TGA/TGD/TGC
        "#;

        let mut rnd = rand::rngs::SmallRng::seed_from_u64(0);
        let trace = AsciWaveTrace::parse(content, &mut rnd);
        let expected_pins = [
            ("ADR_O", 32u32),
            ("DAT_I", 32),
            ("DAT_O", 32),
            ("WE_O", 1),
            ("SEL_O", 4),
            ("STB_O", 1),
            ("ACK_I", 1),
            ("CYC_O", 1),
        ];
        assert_eq!(
            trace.pins.iter().map(|(n, _)| n).collect::<Vec<_>>(),
            expected_pins.iter().map(|(n, _)| *n).collect::<Vec<_>>()
        );
        assert_eq!(
            trace.pins.iter().map(|(_, w)| *w).collect::<Vec<_>>(),
            expected_pins.iter().map(|(_, w)| *w).collect::<Vec<_>>()
        );

        assert_eq!(trace.values[0][1].to_hex_str(), "00001234", "ADR_O");
        assert_eq!(trace.values[0][2].to_hex_str(), "00001234", "ADR_O");
        assert!(trace.values[3].iter().all(|v| v.is_false()), "WE_O");
        assert_eq!(
            trace.values[5]
                .iter()
                .map(|v| v.is_true())
                .collect::<Vec<_>>(),
            [false, true, true, false],
            "STB_O"
        );
        assert_eq!(
            trace.values[6]
                .iter()
                .map(|v| v.is_true())
                .collect::<Vec<_>>(),
            [false, false, true, false],
            "ACK_O"
        );
    }
}
