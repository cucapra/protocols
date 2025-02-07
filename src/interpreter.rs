use verilog::{verilog, VerilatorRuntime};




#[cfg(test)]
pub mod tests {
    use verilog::{PortDirection, VerilatorRuntimeOptions};
    use super::*;

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
            &["examples/tinyaes128/aes_128.v".as_ref(), "examples/tinyaes128/table.v".as_ref()],
            [],
            options,
            false,
        ).unwrap();

        let mut dut = runtime.create_dyn_model(
            "expand_key_128",
            "examples/tinyaes128/aes_128.v",
            &[
                // you should be able to derive these from the struct
                ("in", 127, 0, PortDirection::Input),
                ("out_1", 127, 0, PortDirection::Output),
                ("out_2", 127, 0, PortDirection::Output),
            ],
        ).unwrap();



    }

}