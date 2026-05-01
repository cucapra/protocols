// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Instance;
use baa::{BitVecOps, BitVecValue, WidthInt};
use protocols::design::Design;
use protocols::ir::SymbolId;
use rand::{Rng, SeedableRng};
use rustc_hash::FxHashMap;
use wellen::{Hierarchy, SignalEncoding, SignalRef, Time, Timescale, TimescaleUnit};

/// The result of advancing the clock cycle by one step
#[derive(Debug, PartialEq)]
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
    fn get(&self, instance_id: u32, pin: SymbolId) -> BitVecValue;

    fn step_to_time(&self) -> StepToTime;
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
    port_map: FxHashMap<PortKey, SignalRef>,

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

    /// Maps a logical step to time step.
    step_to_idx: Vec<u32>,
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
            logical_step: 0,
            time_step: 0,
            clock_signal,
            step_to_idx: vec![0],
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
        let design = &designs[&inst.design];

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
                        pin.bitwidth(),
                        "The bit-width of the waveform value is {}, which doesn't match expected width of {}, which is {}",
                        waveform_bits,
                        pin.name(),
                        pin.bitwidth()
                    );

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
                    self.step_to_idx.push(self.time_step);
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
                        self.step_to_idx.push(self.time_step);
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
    fn get(&self, instance_id: u32, pin: SymbolId) -> BitVecValue {
        let key = PortKey {
            instance_id,
            pin_id: pin,
        };
        // Get the Wellen `SignalRef` (akin to `SignalId`)
        let signal_ref = self.port_map.get(&key).unwrap();

        // Obtain the `SignalValue` at the current `time_step`
        // (represented as a bit-string)
        let bit_str = self.get_value(*signal_ref, self.time_step);

        BitVecValue::from_bit_str(&bit_str).unwrap_or_else(|_| {
            // If the bit-string can't be converted into a BitVecValue
            // (e.g. because the waveform contains "x"), generate
            // a random value of the appropriate bit-width.
            let bitwidth = match self.wave.hierarchy().get_signal_tpe(*signal_ref) {
                Some(SignalEncoding::BitVector(width)) => width.get(),
                _ => panic!("Expected a bit-vector signal for key {:?}", key),
            };
            let mut rng = rand::rngs::SmallRng::seed_from_u64(0);
            BitVecValue::random(&mut rng, bitwidth)
        })
    }

    fn step_to_time(&self) -> StepToTime {
        let tt = self.wave.time_table();
        StepToTime {
            logical_step_to_time: self
                .step_to_idx
                .iter()
                .map(|step| tt[*step as usize])
                .collect(),
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
    symbol_map: FxHashMap<(u32, SymbolId), usize>,
    step: u32,
}

impl AsciWaveTrace {
    pub fn open(
        filename: impl AsRef<std::path::Path>,
        designs: &FxHashMap<String, Design>,
        instances: &[Instance],
    ) -> std::io::Result<Self> {
        let mut rnd = rand::rngs::SmallRng::seed_from_u64(0);
        let content = std::fs::read_to_string(filename)?;
        let mut trace = Self::parse(&content, &mut rnd);

        // populate pin map
        for (inst_id, inst) in instances.iter().enumerate() {
            let design = &designs[&inst.design];
            for (pin_id, pin) in design.pins.iter() {
                let name = if inst.name.is_empty() {
                    pin.name().to_string()
                } else {
                    format!("{}.{}", inst.name, pin.name())
                };
                let key = (inst_id as u32, *pin_id);
                if let Some(wave_id) = trace.pins.iter().position(|(n, _)| n == &name) {
                    assert_eq!(
                        trace.pins[wave_id].1,
                        pin.bitwidth(),
                        "Width missmatch for {name}"
                    );
                    trace.symbol_map.insert(key, wave_id);
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
            symbol_map: Default::default(),
            step: 0,
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

fn parse_value(value: &str, width: WidthInt, rnd: &mut impl Rng) -> BitVecValue {
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
    fn step(&mut self) -> StepResult {
        let num_steps = self.values[0].len();
        debug_assert!(self.values.iter().all(|v| v.len() == num_steps));
        if self.step + 1 < num_steps as u32 {
            self.step += 1;
            StepResult::Ok
        } else {
            StepResult::Done
        }
    }

    fn get(&self, instance_id: u32, pin: SymbolId) -> BitVecValue {
        let pin_id = self.symbol_map[&(instance_id, pin)];
        self.values[pin_id][self.step as usize].clone()
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
