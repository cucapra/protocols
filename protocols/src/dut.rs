// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Design Under Test execution and analysis

// TODO: add a trait to allow for an alternative backend that uses Verilator to execute things

use crate::frontend::design::Design;
use crate::frontend::symbol::{Dir, SymbolId};
use crate::yosys::{ProjectConf, YosysEnv, yosys_to_btor};
use anyhow::{Context, bail};
use baa::{BitVecValue, BitVecValueRef};
use patronus::expr::{ExprRef, TypeCheck};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::{Output, TransitionSystem};
use rustc_hash::FxHashMap;
use std::ops::Index;
use std::path::PathBuf;

/// Uniquely identifies a port in the design under test.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct PortId(u32);

pub struct PatronusSim {
    ctx: patronus::expr::Context,
    sys: TransitionSystem,
    sim: Interpreter,
    port_map: FxHashMap<SymbolId, PortId>,
    // Combinational dependency tracking
    /// Maps `input |-> Vec<output>` (outputs that are affected by this input)
    input_dependencies: FxHashMap<PortId, Vec<PortId>>,
    /// Maps each `output |-> Vec<input>` (inputs that this output is dependent on)
    output_dependencies: FxHashMap<PortId, Vec<PortId>>,
}

/// Prototype of our generic (non-patronus specific) dut simulator  interface
impl PatronusSim {
    pub fn new<P: AsRef<std::path::Path>>(
        verilog_paths: &[P],
        top_module: Option<&str>,
        design: &Design,
        waveform_file: Option<&str>,
    ) -> anyhow::Result<Self> {
        let (ctx, sys) = create_sim_context(verilog_paths, top_module);

        let mut sim = if let Some(waveform_file) = waveform_file {
            Interpreter::new_with_wavedump(&ctx, &sys, waveform_file)
        } else {
            Interpreter::new(&ctx, &sys)
        };
        sim.init(InitKind::Zero); // TODO: change to random initialization

        // create port map
        let mut port_map = FxHashMap::default();
        let mut outputs = FxHashMap::default();
        let mut inputs = FxHashMap::default();
        for (pin_idx, pin) in design.pins.iter().enumerate() {
            let (expr, pos) = match pin.dir() {
                Dir::In => {
                    let pos = sys
                        .inputs
                        .iter()
                        .position(|i| ctx.get_symbol_name(*i).unwrap() == pin.name())
                        .context("unable to find input pin")?;
                    (sys.inputs[pos], pos)
                }
                Dir::Out => {
                    let pos = sys
                        .outputs
                        .iter()
                        .position(|o| ctx[o.name] == pin.name())
                        .context("unable to find output pin")?;
                    (sys.outputs[pos].expr, pos + sys.inputs.len())
                }
            };
            let port_id = PortId(pos as u32);
            match pin.dir() {
                Dir::In => inputs.insert(expr, port_id),
                Dir::Out => outputs.insert(expr, port_id),
            };
            let width = expr
                .get_bv_type(&ctx)
                .context("ports must be of bit-vector and not of array type")?;
            if width != pin.bitwidth() {
                bail!(
                    "Width of port `{}` does not match: {width} (Verilog) vs {} (struct)",
                    pin.name(),
                    pin.bitwidth()
                );
            }
            for (_, syms) in &design.protocols {
                port_map.insert(syms[pin_idx], port_id);
            }
        }

        // Build combinational dependency graphs
        let mut output_dependencies = FxHashMap::default();
        let mut input_dependencies = FxHashMap::default();

        // For each output, find all inputs in its combinational cone of influence
        for out in &sys.outputs {
            let input_exprs =
                patronus::system::analysis::cone_of_influence_comb(&ctx, &sys, out.expr);
            let port_out = outputs[&out.expr];
            for input_expr in input_exprs {
                let port_in = inputs[&input_expr];
                // inputs this output depends on
                output_dependencies
                    .entry(port_in)
                    .or_insert_with(Vec::new)
                    .push(port_out);
                // outputs this input affects
                input_dependencies
                    .entry(port_out)
                    .or_insert_with(Vec::new)
                    .push(port_in);
            }
        }

        Ok(Self {
            ctx,
            sys,
            sim,
            port_map,
            input_dependencies,
            output_dependencies,
        })
    }

    /// outputs that depend on the provided input port
    pub fn dependent_outputs(&self, port: PortId) -> impl Iterator<Item = PortId> {
        assert!(
            self.get_input(port).is_some(),
            "only works for input ports!"
        );
        self.input_dependencies[&port].iter().cloned()
    }

    /// inputs that might influence the provided input or output port
    pub fn coi_inputs(&self, port: PortId) -> impl Iterator<Item = PortId> {
        self.output_dependencies[&port].iter().cloned()
    }

    pub fn ios(&self) -> impl Iterator<Item = PortId> {
        (0..self.sys.inputs.len() + self.sys.outputs.len()).map(|i| PortId(i as u32))
    }

    pub fn inputs(&self) -> impl Iterator<Item = PortId> {
        (0..self.sys.inputs.len()).map(|i| PortId(i as u32))
    }

    pub fn outputs(&self) -> impl Iterator<Item = PortId> {
        let offset = self.sys.inputs.len();
        (offset..offset + self.sys.outputs.len()).map(|i| PortId(i as u32))
    }

    pub fn port_width(&self, port: PortId) -> u32 {
        let maybe_w = self
            .get_port_expr(port)
            .and_then(|e| e.get_bv_type(&self.ctx));
        maybe_w.unwrap()
    }

    pub fn port_name(&self, port: PortId) -> &str {
        self.get_port_name(port).unwrap()
    }

    pub fn set<'b>(&mut self, port: PortId, value: impl Into<BitVecValueRef<'b>>) {
        assert!(
            self.get_input(port).is_some(),
            "only works for input ports!"
        );
        self.sim.set(self.get_input(port).unwrap(), value);
    }

    pub fn get(&self, port: PortId) -> BitVecValue {
        let expr = self.get_port_expr(port).expect("invalid port id");
        self.sim
            .get(expr)
            .try_into()
            .expect("all ports should be bit vectors and not arrays!")
    }

    pub fn step(&mut self) {
        self.sim.step();
    }
}

impl Index<SymbolId> for PatronusSim {
    type Output = PortId;

    fn index(&self, index: SymbolId) -> &Self::Output {
        &self.port_map[&index]
    }
}

/// Implementation details.
impl PatronusSim {
    fn get_input(&self, port: PortId) -> Option<ExprRef> {
        self.sys.inputs.get(port.0 as usize).cloned()
    }

    fn get_output(&self, port: PortId) -> Option<Output> {
        if self.get_input(port).is_some() {
            None
        } else {
            self.sys
                .outputs
                .get(port.0 as usize - self.sys.inputs.len())
                .cloned()
        }
    }

    fn get_port_expr(&self, port: PortId) -> Option<ExprRef> {
        self.get_input(port)
            .or_else(|| self.get_output(port).map(|o| o.expr))
    }

    fn get_port_name(&self, port: PortId) -> Option<&str> {
        if let Some(e) = self.get_input(port) {
            self.ctx[e].get_symbol_name(&self.ctx)
        } else if let Some(o) = self.get_output(port) {
            Some(&self.ctx[o.name])
        } else {
            None
        }
    }
}

/// Takes a vec of paths to Verilog files and the name of a top-level module,
/// and returns a (Patronus `Context`, Patronus `TransitionSystem` pair)
fn create_sim_context<P: AsRef<std::path::Path>>(
    verilog_paths: &[P],
    top_module: Option<&str>,
) -> (patronus::expr::Context, TransitionSystem) {
    let env = YosysEnv::default();
    let sources: Vec<PathBuf> = verilog_paths
        .iter()
        .map(|p| PathBuf::from(p.as_ref()))
        .collect();
    let proj = ProjectConf::with_sources(sources, top_module.map(|s| s.into()));

    let btor_file = yosys_to_btor(&env, &proj, None)
        .unwrap_or_else(|e| panic!("Failed to convert Verilog to BTOR: {}", e));

    // Check if btor file was actually created and has content
    if !btor_file.exists() {
        panic!("BTOR file was not created at path: {}", btor_file.display());
    }

    let metadata = std::fs::metadata(&btor_file)
        .unwrap_or_else(|e| panic!("Failed to read BTOR file metadata: {}", e));

    if metadata.len() == 0 {
        panic!("BTOR file is empty - likely synthesis failed. Check Yosys output for errors.");
    }

    patronus::btor2::parse_file(btor_file.as_path().as_os_str()).unwrap_or_else(|| {
        panic!(
            "Failed to parse BTOR file - possibly malformed: {}",
            btor_file.display()
        )
    })
}
