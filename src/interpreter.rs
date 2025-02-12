use marlin_verilator::*;

#[cfg(test)]
pub mod tests {
    use super::*;
    use baa::BitVecValue;
    use patronus::sim::Simulator;

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

        let mut dut = runtime
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

        let mut dut = runtime
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
    fn run_add_d1_with_patronus() {
        let (ctx, sys) = patronus::btor2::parse_file("examples/adders/add_d1.btor").unwrap();
        let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);
        let a = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "A")
            .unwrap();
        let b = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == "B")
            .unwrap();
        let s = sys
            .outputs
            .iter()
            .find(|o| ctx[o.name] == "S")
            .unwrap()
            .expr;

        sim.set(a, &BitVecValue::from_u64(1, 32));
        sim.set(b, &BitVecValue::from_u64(3, 32));
        sim.step();
        assert_eq!(sim.get(s).unwrap(), 4);
    }
}
