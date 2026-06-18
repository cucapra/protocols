// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Design Under Test execution and analysis

// TODO: add a trait to allow for an alternative backend that uses Verilator to execute things

use crate::frontend::design::Design;
use crate::frontend::symbol::SymbolId;
use crate::yosys::{ProjectConf, YosysEnv, yosys_to_btor};
use baa::{BitVecValue, BitVecValueRef};
use patronus::expr::{Context, ExprRef, TypeCheck};
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::{Output, TransitionSystem};
use rustc_hash::FxHashMap;
use std::ops::Index;
use std::path::PathBuf;

/// Uniquely identifies a port in the design under test.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct PortId(u32);

pub struct PatronusSim {
    ctx: Context,
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
    ) -> Self {
        let (ctx, sys) = create_sim_context(verilog_paths, top_module);

        let mut sim = if let Some(waveform_file) = waveform_file {
            Interpreter::new_with_wavedump(&ctx, &sys, waveform_file)
        } else {
            Interpreter::new(&ctx, &sys)
        };
        sim.init(InitKind::Zero); // TODO: change to random initialization

        // let mut input_mapping = FxHashMap::default();
        // let mut output_mapping = FxHashMap::default();
        //
        // for symbol_id in dut_symbols {
        //     let sym = &st[symbol_id];
        //     if sym.is_in_port() {
        //         let input = sys
        //             .inputs
        //             .iter()
        //             .find(|i| ctx.get_symbol_name(**i).unwrap() == sym.name())
        //             .unwrap_or_else(|| {
        //                 panic!(
        //                     "Failed to find input with name '{}'. Available inputs: {:?}",
        //                     sym.name(),
        //                     sys.inputs
        //                         .iter()
        //                         .map(|o| ctx.get_symbol_name(*o).unwrap())
        //                         .collect::<Vec<_>>()
        //                 )
        //             });
        //         input_mapping.insert(*symbol_id, *input);
        //     }
        //     if sym.is_out_port() {
        //         // check if the DUT symbol is an output
        //         let output = sys
        //             .outputs
        //             .iter()
        //             .find(|o| ctx[o.name] == sym.name())
        //             .unwrap_or_else(|| {
        //                 panic!(
        //                     "Failed to find output with name '{}' in system outputs. Available outputs: {:?}",
        //                     sym.name(),
        //                     sys.outputs.iter().map(|o| &ctx[o.name]).collect::<Vec<_>>()
        //                 )
        //             });
        //         output_mapping.insert(*symbol_id, *output);
        //     }
        // }

        // Build combinational dependency graphs
        // let mut output_dependencies: FxHashMap<SymbolId, Vec<SymbolId>> = FxHashMap::default();
        // let mut input_dependencies: FxHashMap<SymbolId, Vec<SymbolId>> = FxHashMap::default();
        //
        // // Initialize: keys are outputs -> inputs dependent on that ouput, and inputs -> all combinationally dependent outputs
        // for symbol_id in output_mapping.keys() {
        //     output_dependencies.insert(*symbol_id, Vec::new());
        // }
        // for symbol_id in input_mapping.keys() {
        //     input_dependencies.insert(*symbol_id, Vec::new());
        // }

        // For each output, find all inputs in its combinational cone of influence
        // for (out_sym, out) in &output_mapping {
        //     let input_exprs =
        //         patronus::system::analysis::cone_of_influence_comb(ctx, sys, out.expr);
        //     for input_expr in input_exprs {
        //         // Find the protocol symbol corresponding to this input expression
        //         if let Some(input_sym) = input_mapping
        //             .iter()
        //             .find_map(|(k, v)| if *v == input_expr { Some(*k) } else { None })
        //         {
        //             // output_dependencies: output -> Vec<input> (inputs this output depends on)
        //             if let Some(vec) = output_dependencies.get_mut(out_sym) {
        //                 vec.push(input_sym);
        //             }
        //             // input_dependencies: input -> Vec<output> (outputs this input affects)
        //             if let Some(vec) = input_dependencies.get_mut(&input_sym) {
        //                 vec.push(*out_sym);
        //             }
        //         }
        //     }
        // }

        todo!()
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
) -> (Context, TransitionSystem) {
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
