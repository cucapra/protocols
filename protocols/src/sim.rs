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
    use marlin_verilator::dynamic::DynamicVerilatedModel;
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
        let (clk, rcon, inp, out_1, out_2) = ("clk", "rcon", "in", "out_1", "out_2");
        let mut dut = runtime
            .create_dyn_model(
                "expand_key_128",
                "../examples/tinyaes128/aes_128.v",
                &[
                    // you should be able to derive these from the struct
                    (clk, 0, 0, PortDirection::Input),
                    (rcon, 7, 0, PortDirection::Input),
                    (inp, 127, 0, PortDirection::Input),
                    (out_1, 127, 0, PortDirection::Output),
                    (out_2, 127, 0, PortDirection::Output),
                ],
                conf,
            )
            .unwrap();

        let step = |dut: &mut DynamicVerilatedModel| {
            dut.pin(clk, 1u8).unwrap();
            dut.eval();
            dut.pin(clk, 0u8).unwrap();
        };

        // execute an expand_key
        let inp_value = [0u32; 4];
        dut.pin(inp, &inp_value).unwrap();
        dut.pin(rcon, 1u8).unwrap(); // rcon is a constant for the circuit
        dut.pin(clk, 0u8).unwrap();
        dut.eval();
        step(&mut dut);

        let inp_value_2 = [11u32; 4];
        dut.pin(inp, &inp_value_2).unwrap(); // X
        dut.eval();
        let out_1_val = dut.read(out_1).unwrap();
        println!("out_1 = {out_1_val:?}");
        step(&mut dut);

        dut.pin(inp, &inp_value_2).unwrap(); // X
        dut.eval();
        let out_2_val = dut.read(out_2).unwrap();
        println!("out_2 = {out_2_val:?}");
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
