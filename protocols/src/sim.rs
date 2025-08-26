// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Verilog simulators used by the interpreter

pub trait Simulation {}

#[derive(Debug)]
pub struct PatronusSim {}

impl Simulation for PatronusSim {}

#[derive(Debug)]
pub struct VerilatorSim {}

impl Simulation for VerilatorSim {}

#[cfg(test)]
pub mod tests {
    use crate::yosys::*;
    use baa::{BitVecOps, BitVecValue};
    use marlin_verilator::*;
    use patronus::sim::Simulator;
    use std::path::PathBuf;

    /// This example is intended to demonstrate how the `verilog` crate can be used
    /// to execute a design with Verilator. This is - of course - not a working
    /// interpreter, just a tech demo that shows the foundations that the interpreter could
    /// be built on.
    #[test]
    fn run_aes128_key_expand_with_verilator() {
        let options = VerilatorRuntimeOptions::default();
        let mut runtime = VerilatorRuntime::new(
            "test_run".into(),
            &["../examples/tinyaes128/aes_128.v".as_ref()],
            &[],
            [],
            options,
        )
        .unwrap();

        let conf = VerilatedModelConfig::default();
        let _dut = runtime
            .create_dyn_model(
                "expand_key_128",
                "../examples/tinyaes128/aes_128.v",
                &[
                    // you should be able to derive these from the struct
                    ("in", 127, 0, PortDirection::Input),
                    ("out_1", 127, 0, PortDirection::Output),
                    ("out_2", 127, 0, PortDirection::Output),
                ],
                conf,
            )
            .unwrap();
    }

    #[test]
    fn run_add_d1_with_verilator() {
        let options = VerilatorRuntimeOptions::default();
        let mut runtime = VerilatorRuntime::new(
            "test_run".into(),
            &["tests/adders/adder_d1/add_d1.v".as_ref()],
            &[],
            [],
            options,
        )
        .unwrap();

        let conf = VerilatedModelConfig::default();
        let dut = runtime
            .create_dyn_model(
                "adder_d1",
                "tests/adders/adder_d1/add_d1.v",
                &[
                    // you should be able to derive these from the struct
                    ("a", 31, 0, PortDirection::Input),
                    ("b", 31, 0, PortDirection::Input),
                    ("s", 31, 0, PortDirection::Output),
                ],
                conf,
            )
            .unwrap();
    }
}
