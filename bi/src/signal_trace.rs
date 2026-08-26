// Copyright 2025-26 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Instance;
use baa::{BitVecMutOps, BitVecOps, BitVecValue, BitVecValueRef, WidthInt};
use protocols::frontend::Module;
use protocols::frontend::symbol::{SymbolId, SymbolTable};
use rand::{Rng, SeedableRng};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::io::BufReader;
use wellen::stream::StreamError;
use wellen::{Hierarchy, ItemRef, SignalRef, SignalValueRef, Time, Timescale, TimescaleUnit};

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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CallbackResult {
    Continue,
    Stop,
}

/// Provides a trace of signals that we can analyze.
pub trait SignalTrace {
    /// Streams time steps.
    fn stream_steps(
        &mut self,
        callback: impl FnMut(u32, SignalValues) -> CallbackResult,
    ) -> Result<(), String>;

    fn step_to_time(&self) -> StepToTime;
}

/// The `WaveSamplingMode` determines how signals from a waveform are sampled
#[derive(Debug, Clone)]
pub enum WaveSamplingMode {
    /// Sample on the rising edge of the signal
    RisingEdge(String),
    /// Sample on the falling edge of the signal
    FallingEdge(String),
    /// Interpret every time step as a new clock step. This generally only works
    /// for waveforms produced by the Patronus simulator.
    Direct,
}

/// A `WaveSamplingMode` with the clock name replaced by its `SignalRef`.
#[derive(Debug, Clone)]
enum SamplingMode {
    RisingEdge(SignalRef),
    FallingEdge(SignalRef),
    /// We include the timetable in order to faithfully include steps with no signal changes.
    Direct(Vec<Time>),
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
    /// signal names for debugging
    names: Vec<String>,

    /// The sampling mode to be used on the waveform
    sampling_mode: SamplingMode,

    /// The current (logical) `step()` in the Protocols specification
    logical_step: u32,

    /// The actual clock time-step in the waveform
    time_step: u32,

    /// Maps a logical step to time.
    logical_step_to_time: Vec<Time>,

    force_x_to_zero: bool,
}

/// A `PortKey` is just a pair consisting of an `instance_id` and a `symbol_id` for a pin
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PortKey {
    pub instance_id: u32,
    pub pin_id: SymbolId,
}

fn load_time_table(filename: &impl AsRef<std::path::Path>) -> Vec<Time> {
    wellen::simple::read(filename)
        .unwrap()
        .time_table()
        .to_vec()
}

impl WaveSignalTrace {
    /// Opens a waveform at the specified `filename` with the given
    /// `Design`s and `Instance`s. The CLI arg `sample_posedge` is passed
    /// as an argument to determine the `WaveSamplingMode` (whether it is
    /// `Direct` or `RisingEdge`).
    pub fn open(
        filename: &impl AsRef<std::path::Path>,
        st: &SymbolTable,
        modules: &[Module],
        instances: &[Instance],
        sampling_mode: WaveSamplingMode,
        force_x_to_zero: bool,
    ) -> Result<Self, wellen::WellenError> {
        let opts = wellen::LoadOptions::default();
        let wave = wellen::stream::read_from_file(filename, &opts)?;

        // find instances in the waveform hierarchy
        let (port_to_signal, sampling_mode) =
            find_instances(wave.hierarchy(), modules, instances, sampling_mode);

        // for direct sampling, we need to add the time table
        let sampling_mode = match sampling_mode {
            SamplingMode::Direct(_) => {
                let mut time_table = load_time_table(filename);
                // traditionally, the last time step is not actually emitted
                // TODO: should we change this?
                time_table.pop();
                SamplingMode::Direct(time_table)
            }
            other => other,
        };

        // load all relavant signal references into memory
        let mut signals: Vec<SignalRef> = port_to_signal.values().cloned().collect();
        // Add clock signal if present
        if let SamplingMode::RisingEdge(clk_sig) | SamplingMode::FallingEdge(clk_sig) =
            sampling_mode
        {
            signals.push(clk_sig);
        } else {
            debug_assert!(matches!(sampling_mode, SamplingMode::Direct(_)));
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

        // name lookup for debugging
        let signal_to_port: FxHashMap<_, _> =
            port_to_signal.iter().map(|(k, v)| (*v, *k)).collect();
        let names = signals
            .iter()
            .map(|s| {
                signal_to_port
                    .get(s)
                    .map(|p| st[p.pin_id].name().to_string())
                    .unwrap_or_default()
            })
            .collect();

        Ok(Self {
            wave,
            port_map,
            signal_ref_to_idx,
            signals,
            sampling_mode,
            logical_step: 0,
            time_step: 0,
            logical_step_to_time: vec![],
            names,
            force_x_to_zero,
        })
    }
}

/// Checks instances and returns a pair consisting of the (port map, optional clock signal)
/// (the latter is only `Some` if `sample_posedge` corresponds to a valid signal)
fn find_instances(
    hierachy: &Hierarchy,
    modules: &[Module],
    instances: &[Instance],
    sampling_mode: WaveSamplingMode,
) -> (FxHashMap<PortKey, SignalRef>, SamplingMode) {
    let mut port_map = FxHashMap::default();

    // find clock signal
    let samp_mode_out = match &sampling_mode {
        WaveSamplingMode::RisingEdge(signal_name) | WaveSamplingMode::FallingEdge(signal_name) => {
            let signal_ref = if let Some(item) = hierachy.lookup_item_by_name(signal_name) {
                if let ItemRef::Var(var) = item {
                    hierachy[var].signal_ref()
                } else {
                    panic!("Clock `{signal_name}` is a scope, not a particular signal!")
                }
            } else {
                panic!("Failed to find clock signal {signal_name}");
            };
            if matches!(sampling_mode, WaveSamplingMode::RisingEdge(_)) {
                SamplingMode::RisingEdge(signal_ref)
            } else {
                SamplingMode::FallingEdge(signal_ref)
            }
        }
        WaveSamplingMode::Direct => SamplingMode::Direct(vec![]),
    };

    // find instance pins
    for (inst_id, inst) in instances.iter().enumerate() {
        let module = &modules[inst.module_id];

        // check to make sure the instance scope actually exists
        let inst_scope = if !inst.name.is_empty() {
            let inst_name_parts: Vec<&str> = inst.name.split('.').collect();
            if let Some(scope) = hierachy.lookup_scope(&inst_name_parts) {
                Some(scope)
            } else {
                panic!(
                    "Failed to find instance {}. First scope: {:#?}",
                    inst.name,
                    hierachy.first_scope().map(|s| s.full_name(hierachy))
                );
            }
        } else {
            None
        };

        // for every pin designed in our struct, we have to find the correct
        // variable that corresponds to it
        for (field_idx, field) in module.pins.iter().enumerate() {
            let pin_name = field.name().to_string();
            let full_name = if inst.name.is_empty() {
                pin_name.clone()
            } else {
                format!("{}.{pin_name}", inst.name)
            };
            // find a variable that has a matching name
            if let Some(ItemRef::Var(var)) = hierachy.lookup_item_by_name(&full_name) {
                let waveform_bits = hierachy[var].length(hierachy).expect("not a bit vector");

                // Check that bit widths match
                assert_eq!(
                    waveform_bits,
                    field.bitwidth(),
                    "The bit-width of the waveform signal `{full_name}` does not match the width of the pin `{pin_name}` in `{}`",
                    module.name,
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
                let available_vars: Vec<&str> = inst_scope
                    .map(|s| {
                        hierachy[s]
                            .vars(hierachy)
                            .map(|v| hierachy[v].name(hierachy))
                            .collect()
                    })
                    .unwrap_or_else(|| {
                        hierachy
                            .vars()
                            .map(|v| hierachy[v].name(hierachy))
                            .collect()
                    });

                panic!(
                    "Failed to find pin {}. Available pins in waveform for instance {} are {}",
                    field.name(),
                    inst.name,
                    available_vars.join(",\n")
                );
            }
        }
    }
    (port_map, samp_mode_out)
}

impl SignalTrace for WaveSignalTrace {
    fn stream_steps(
        &mut self,
        mut callback: impl FnMut(u32, SignalValues) -> CallbackResult,
    ) -> Result<(), String> {
        let signals = self.signals.clone();
        // random initial values
        let mut rng = RefCell::new(rand::rngs::SmallRng::seed_from_u64(0));
        let widths: Vec<_> = signals
            .iter()
            .map(|s| {
                self.wave
                    .hierarchy()
                    .get_signal_tpe(*s)
                    .unwrap()
                    .length()
                    .unwrap()
            })
            .collect();
        let mut bv_values: Vec<_> = widths
            .iter()
            .map(|&width| {
                if self.force_x_to_zero {
                    BitVecValue::zero(width)
                } else {
                    BitVecValue::random(rng.get_mut(), width)
                }
            })
            .collect();
        let mut times = vec![];
        let filter = wellen::stream::Filter::include_signals(&signals);
        let mut step_id = 0;
        let mut prev_clock = false;
        let stream_result = self
            .wave
            .stream_time_steps::<()>(filter, |time, values, changed| {
                let is_step = match &self.sampling_mode {
                    SamplingMode::RisingEdge(clock) => {
                        let current_clock: bool = values.get(clock).unwrap().try_into().unwrap();
                        let is_rising_edge = !prev_clock && current_clock;
                        prev_clock = current_clock;
                        // we always include the first time step, even if there is not an edge
                        let is_first_step = times.is_empty();
                        is_rising_edge || is_first_step
                    }
                    SamplingMode::FallingEdge(clock) => {
                        let current_clock: bool = values.get(clock).unwrap().try_into().unwrap();
                        let is_falling_edge = prev_clock && !current_clock;
                        prev_clock = current_clock;
                        // we always include the first time step, even if there is not an edge
                        let is_first_step = times.is_empty();
                        is_falling_edge || is_first_step
                    }
                    SamplingMode::Direct(_) => {
                        // are there any time steps we have missed?
                        if let Some(prev_time) = times.last().cloned()
                            && time > prev_time + 1
                        {
                            for time in prev_time + 1..time {
                                times.push(time);
                                let r = callback(
                                    step_id,
                                    SignalValues {
                                        port_map: &self.port_map,
                                        values: &bv_values,
                                    },
                                );
                                if r == CallbackResult::Stop {
                                    return Err(());
                                }
                                step_id += 1;
                            }
                        }
                        true
                    }
                };

                // we record all changed values, even if they change between steps
                for s in changed {
                    if let SamplingMode::RisingEdge(clock) = &self.sampling_mode
                        && s == clock
                    {
                        continue; // skip clock
                    }
                    let idx = self.signal_ref_to_idx[s];
                    let value_ref = values.get(s).unwrap();
                    if let SignalValueRef::BitVec(value) = value_ref {
                        if let Some(value_be_bytes) = value.be_bytes() {
                            bv_values[idx].assign_from_bytes_be(value_be_bytes);
                        } else {
                            // there are X or Z values
                            let all_x_or_z =
                                value.bit_string().chars().all(|c| c == 'x' || c == 'z');
                            if !all_x_or_z {
                                println!("WARN: encountered a mixed value. Randomizing all bits.");
                                println!("{}@{step_id}={}", self.names[idx], value.bit_string());
                            }
                            // randomize
                            let width = widths[idx];
                            let random_value = if self.force_x_to_zero {
                                BitVecValue::zero(width)
                            } else {
                                BitVecValue::random(rng.get_mut(), width)
                            };
                            bv_values[idx].assign(&random_value);
                        }
                    } else {
                        unreachable!("we only expect bit vectors");
                    }
                }

                if is_step {
                    // println!("Step {step_id}:");
                    // for (idx, name) in self.names.iter().enumerate() {
                    //     if !name.is_empty() {
                    //         println!(" - {name}: {}", bv_values[idx].to_hex_str());
                    //     }
                    // }

                    times.push(time);
                    let r = callback(
                        step_id,
                        SignalValues {
                            port_map: &self.port_map,
                            values: &bv_values,
                        },
                    );
                    if r == CallbackResult::Stop {
                        return Err(());
                    }
                    step_id += 1;
                }
                Ok(())
            });
        match stream_result {
            Ok(_) => {}
            // our pseudo error just indicates that we wanted to stop streaming early
            Err(StreamError::Callback(_)) => {}
            // an error reading the file
            Err(StreamError::Wellen(e)) => return Err(e.to_string()),
        }
        if let SamplingMode::Direct(time_table) = &self.sampling_mode
            && time_table.last().cloned().unwrap_or_default() > times.last().cloned().unwrap()
        {
            let last_time = *times.last().unwrap();
            // are the time steps that have not been dispatched yet?
            if let Some(larger_time_idx) = time_table.iter().position(|e| *e > last_time) {
                for time in &time_table[larger_time_idx..] {
                    times.push(*time);
                    let r = callback(
                        step_id,
                        SignalValues {
                            port_map: &self.port_map,
                            values: &bv_values,
                        },
                    );
                    if r == CallbackResult::Stop {
                        break;
                    }
                    step_id += 1;
                }
            }
        }

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
        force_x_to_zero: bool,
    ) -> std::io::Result<Self> {
        let mut rnd = rand::rngs::SmallRng::seed_from_u64(0);
        let content = std::fs::read_to_string(filename)?;
        let mut trace = Self::parse(&content, &mut rnd, force_x_to_zero);

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

    pub fn parse(content: &str, rnd: &mut impl Rng, force_x_to_zero: bool) -> Self {
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
            let (name, width, mut values) = parse_signal_line(line, rnd, force_x_to_zero);
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

fn parse_signal_line(
    line: &str,
    rnd: &mut impl Rng,
    force_x_to_zero: bool,
) -> (String, WidthInt, Vec<BitVecValue>) {
    let tokens = tokenize(line);
    assert!(!tokens.is_empty());
    let (name, width) = parse_name_and_width(tokens[0]);
    let values = tokens
        .into_iter()
        .skip(1)
        .map(|t| parse_value(t, width, rnd, force_x_to_zero))
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

fn parse_value(
    value: &str,
    width: WidthInt,
    rnd: &mut impl rand::Rng,
    force_x_to_zero: bool,
) -> BitVecValue {
    let value = value.to_lowercase();
    let r = if value == "x" {
        if force_x_to_zero {
            BitVecValue::zero(width)
        } else {
            BitVecValue::random(rnd, width)
        }
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
    fn stream_steps(
        &mut self,
        mut callback: impl FnMut(u32, SignalValues) -> CallbackResult,
    ) -> Result<(), String> {
        let num_steps = self.values[0].len();
        debug_assert!(self.values.iter().all(|v| v.len() == num_steps));
        for step in 0..num_steps {
            let bv_values: Vec<_> = self.values.iter().map(|v| v[step].clone()).collect();
            let r = callback(
                step as u32,
                SignalValues {
                    port_map: &self.port_map,
                    values: &bv_values,
                },
            );
            if r == CallbackResult::Stop {
                return Ok(());
            }
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
        let trace = AsciWaveTrace::parse(content, &mut rnd, false);
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
