// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, BitVecValue};
use patronus::expr::{Context, ExprRef};
use patronus::sim::Simulator;
use patronus::system::{Output, TransitionSystem};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::ops::Index;
use std::path::Path;

#[derive(Debug)]
pub struct FunctionalModel {
    sys: TransitionSystem,
    method_names: FxHashMap<String, MethodId>,
    methods: Vec<Method>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct MethodId(u32);

#[derive(Debug)]
pub struct Method {
    id: MethodId,
    name: String,
    guard: ExprRef,
    commit: ExprRef,
    inputs: Vec<(String, ExprRef)>,
    outputs: Vec<(String, ExprRef)>,
}

impl FunctionalModel {
    pub fn load(ctx: &mut Context, reader: &mut impl std::io::BufRead) -> std::io::Result<Self> {
        let m: FunctionalModelJson = serde_json::from_reader(reader)?;
        let sys = patronus::btor2::parse_str(ctx, &m.sys, Some(&m.info.name)).unwrap();
        let methods: Vec<_> = m
            .info
            .methods
            .into_iter()
            .enumerate()
            .map(|(idx, name)| {
                let id = MethodId(idx as u32);
                let guard = sys
                    .lookup_output(ctx, &format!("{name}_guard"))
                    .expect("Failed to find guard output.");
                let commit = sys
                    .lookup_input(ctx, &format!("{name}_commit"))
                    .expect("Failed to find commit input.");
                let input_prefix = format!("{name}_in_");
                let inputs = sys
                    .inputs
                    .iter()
                    .filter_map(|i| {
                        ctx.get_symbol_name(*i)
                            .and_then(|name| name.strip_prefix(&input_prefix))
                            .map(|name| (name.to_string(), *i))
                    })
                    .collect();
                let output_prefix = format!("{name}_out_");
                let outputs = sys
                    .outputs
                    .iter()
                    .filter_map(|o| {
                        ctx[o.name]
                            .strip_prefix(&output_prefix)
                            .map(|name| (name.to_string(), o.expr))
                    })
                    .collect();
                Method {
                    id,
                    name,
                    guard,
                    commit,
                    inputs,
                    outputs,
                }
            })
            .collect();
        let method_names = methods
            .iter()
            .enumerate()
            .map(|(idx, m)| (m.name.to_string(), MethodId(idx as u32)))
            .collect();
        Ok(Self {
            sys,
            methods,
            method_names,
        })
    }

    pub fn name(&self) -> &str {
        &self.sys.name
    }

    pub fn sys(&self) -> &TransitionSystem {
        &self.sys
    }

    pub fn method_id(&self, name: &str) -> Option<MethodId> {
        self.method_names.get(name).cloned()
    }

    pub fn method(&self, name: &str) -> Option<&Method> {
        self.method_id(name).map(|id| &self[id])
    }
}

impl Index<MethodId> for FunctionalModel {
    type Output = Method;

    fn index(&self, index: MethodId) -> &Self::Output {
        &self.methods[index.0 as usize]
    }
}

pub struct FunctionalModelSimulator {
    model: FunctionalModel,
    sim: patronus::sim::Interpreter,
    tru: BitVecValue,
    fals: BitVecValue,
    init_snapshot: u32,
}

impl FunctionalModelSimulator {
    pub fn from_file(filename: impl AsRef<Path>) -> std::io::Result<Self> {
        let file = std::fs::File::open(filename)?;
        let mut reader = std::io::BufReader::new(file);
        Self::load(&mut reader)
    }

    pub fn load(reader: &mut impl std::io::BufRead) -> std::io::Result<Self> {
        let mut ctx = Context::default();
        let model = FunctionalModel::load(&mut ctx, reader)?;
        Ok(Self::new(&mut ctx, model))
    }

    pub fn new(ctx: &Context, model: FunctionalModel) -> Self {
        let mut sim = patronus::sim::Interpreter::new(ctx, &model.sys);
        let init_snapshot = sim.take_snapshot();
        let tru = BitVecValue::from_bool(true);
        let fals = BitVecValue::from_bool(false);
        Self {
            sim,
            model,
            tru,
            fals,
            init_snapshot,
        }
    }

    pub fn name(&self) -> &str {
        self.model.name()
    }

    pub fn guard(&self, method: MethodId) -> bool {
        let e = self.model[method].guard;
        let bv: BitVecValue = self.sim.get(e).try_into().unwrap();
        bv.is_bit_set(0)
    }

    pub fn commit(&mut self, method: MethodId) {
        let e = self.model[method].commit;
        debug_assert!(self.guard(method), "method is not available!");
        self.sim.set(e, &self.tru);
        self.sim.step();
        self.sim.set(e, &self.fals);
    }

    pub fn set_input(&mut self, method: MethodId) {
        todo!()
    }

    pub fn get_output(&self, method: MethodId) {
        todo!()
    }

    pub fn reset(&mut self) {
        self.sim.restore_snapshot(self.init_snapshot);
    }
}

#[derive(Debug)]
pub struct Transaction {
    pub name: String,
    pub commit: Vec<ExprRef>,
    pub inputs: Vec<ExprRef>,
    pub outputs: Vec<Output>,
}

#[derive(Debug, Deserialize, Serialize)]
struct FunctionalModelJson {
    info: FunctionalModelInfoJson,
    sys: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct FunctionalModelInfoJson {
    name: String,
    methods: Vec<String>,
    states: Vec<String>,
}

#[cfg(test)]
pub mod tests {
    use super::*;

    const MUL_JSON: &[u8] = r##"{"info": {"name": "picorv32_pcpi_mul", "methods": ["pcpi_mul", "pcpi_mulh", "pcpi_mulhu", "pcpi_mulhsu"], "states": []}, "sys": "; btor2 description of `picorv32_pcpi_mul` generated by patronus 0.39.4\n1 sort bitvec 1\n2 input 1 pcpi_mul_commit\n3 sort bitvec 32\n4 input 3 pcpi_mul_in_rs1_data\n5 input 3 pcpi_mul_in_rs2_data\n6 input 1 pcpi_mulh_commit\n7 input 3 pcpi_mulh_in_rs1_data\n8 input 3 pcpi_mulh_in_rs2_data\n9 input 1 pcpi_mulhu_commit\n10 input 3 pcpi_mulhu_in_rs1_data\n11 input 3 pcpi_mulhu_in_rs2_data\n12 input 1 pcpi_mulhsu_commit\n13 input 3 pcpi_mulhsu_in_rs1_data\n14 input 3 pcpi_mulhsu_in_rs2_data\n15 one 1\n16 output 15 pcpi_mul_guard\n17 mul 3 4 5\n18 output 17 pcpi_mul_out_rd_data\n19 output 15 pcpi_mulh_guard\n20 sort bitvec 64\n21 sext 20 7 32\n22 sext 20 8 32\n23 mul 20 21 22\n24 slice 3 23 63 32\n25 output 24 pcpi_mulh_out_rd_data\n26 output 15 pcpi_mulhu_guard\n27 uext 20 10 32\n28 uext 20 11 32\n29 mul 20 27 28\n30 slice 3 29 63 32\n31 output 30 pcpi_mulhu_out_rd_data\n32 output 15 pcpi_mulhsu_guard\n33 sext 20 13 32\n34 uext 20 14 32\n35 mul 20 33 34\n36 slice 3 35 63 32\n37 output 36 pcpi_mulhsu_out_rd_data\n"}"##.as_bytes();

    #[test]
    fn test_load_mul_json() {
        let mut ctx = Context::default();
        let m = FunctionalModel::load(&mut ctx, &mut std::io::Cursor::new(MUL_JSON)).unwrap();
        assert_eq!(m.name(), "picorv32_pcpi_mul");
        for name in ["pcpi_mul", "pcpi_mulh", "pcpi_mulhu", "pcpi_mulhsu"] {
            let method = m.method(name).unwrap();
            assert_eq!(method.inputs[0].0, "rs1_data");
            assert_eq!(method.inputs[1].0, "rs2_data");
            assert_eq!(method.outputs[0].0, "rd_data");
            assert_eq!(method.guard, ctx.get_true());
        }
    }

    #[test]
    fn test_sim() {
        let mut sim = FunctionalModelSimulator::load(&mut std::io::Cursor::new(MUL_JSON)).unwrap();
    }
}
