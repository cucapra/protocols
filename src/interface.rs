// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

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
    #[ignore] // unfortunately the `verilator` library does not currently support ports wider than 64 bit
    fn run_aes128_key_expand_with_verilator() {
        let options = VerilatorRuntimeOptions::default();
        let mut runtime = VerilatorRuntime::new(
            "test_run".into(),
            &[
                "examples/tinyaes128/aes_128.v".as_ref(),
                "examples/tinyaes128/table.v".as_ref(),
            ],
            [],
            options,
            false,
        )
        .unwrap();

        let _dut = runtime
            .create_dyn_model(
                "expand_key_128",
                "examples/tinyaes128/aes_128.v",
                &[
                    // you should be able to derive these from the struct
                    ("in", 127, 0, PortDirection::Input),
                    ("out_1", 127, 0, PortDirection::Output),
                    ("out_2", 127, 0, PortDirection::Output),
                ],
            )
            .unwrap();
    }

    #[test]
    #[ignore]
    fn run_add_d1_with_verilator() {
        let options = VerilatorRuntimeOptions::default();
        let mut runtime = VerilatorRuntime::new(
            "test_run".into(),
            &["examples/adders/add_d1.v".as_ref()],
            [],
            options,
            false,
        )
        .unwrap();

        let _dut = runtime
            .create_dyn_model(
                "adder_d1",
                "examples/adders/add_d1.v",
                &[
                    // you should be able to derive these from the struct
                    ("A", 31, 0, PortDirection::Input),
                    ("B", 31, 0, PortDirection::Input),
                    ("S", 31, 0, PortDirection::Output),
                ],
            )
            .unwrap();
    }

    #[test]
    #[ignore]
    fn run_mult_d0_patronus() {
        let (ctx, sys) = patronus::btor2::parse_file("examples/multipliers/mult_d0.btor").unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let a = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "a")
            .unwrap();
        let b = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "b")
            .unwrap();
        let s = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "s")
            .unwrap()
            .expr;

        sim.init();
        sim.set(a, &BitVecValue::from_u64(6, 32));
        sim.set(b, &BitVecValue::from_u64(7, 32));
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 42);
    }

    #[test]
    #[ignore]
    fn run_add_d0_with_patronus() {
        let (ctx, sys) = patronus::btor2::parse_file("examples/adders/add_d0.btor").unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

        let a = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "a")
            .unwrap();
        let b = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "b")
            .unwrap();
        let s = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "s")
            .unwrap()
            .expr;

        sim.init();
        sim.set(a, &BitVecValue::from_u64(41, 32));
        sim.set(b, &BitVecValue::from_u64(59, 32));
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 100);
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 100); // First step should keep value
    }

    #[test]
    #[ignore]
    fn run_add_d1_with_patronus() {
        let (ctx, sys) = patronus::btor2::parse_file("examples/adders/add_d1.btor").unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

        let a = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "a")
            .unwrap();
        let b = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "b")
            .unwrap();
        let s = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "s")
            .unwrap()
            .expr;

        sim.init();
        sim.set(a, &BitVecValue::from_u64(4, 32));
        sim.set(b, &BitVecValue::from_u64(6, 32));
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 0);
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 10); // First step should have value
    }

    #[test]
    #[ignore]
    fn run_add_d2_with_patronus() {
        let (ctx, sys) = patronus::btor2::parse_file("examples/adders/add_d2.btor").unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

        let a = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "a")
            .unwrap();
        let b = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "b")
            .unwrap();
        let s = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "s")
            .unwrap()
            .expr;

        sim.init();
        sim.set(a, &BitVecValue::from_u64(10, 32));
        sim.set(b, &BitVecValue::from_u64(5, 32));
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 0); // No step should be nothing
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 0); // First step should be nothing
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 15); // Register should now have value
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 15); // Register should keep value
    }

    #[test]
    #[ignore]
    fn run_counter_with_patronus() {
        let env = YosysEnv::default();
        let inp = PathBuf::from("examples/counter/counter.v");
        let mut proj = ProjectConf::with_source(inp);
        let btor_file = yosys_to_btor(&env, &proj, None).unwrap();

        let (ctx, sys) = patronus::btor2::parse_file(btor_file.as_path().as_os_str()).unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

        let c = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "c")
            .unwrap()
            .expr;

        sim.init();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 0);
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 1);
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 2);
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 3);
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 4);
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 5);
        sim.step();
        sim.step();
        sim.step();
        sim.step();
        sim.step();
        sim.step();
        assert_eq!(sim.get(c).unwrap().to_u64().unwrap(), 0); // Reseting to 0
    }
}
