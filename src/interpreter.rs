use crate::ir::*;
use baa::BitVecValue;
use marlin_verilator::*;
use patronus::sim::{Interpreter, Simulator};

use std::collections::HashMap;

fn mapping(tr: &Transaction, st: &SymbolTable, stmtid: &StmtId, sim: &mut Interpreter) {
    match &tr[stmtid] {
        Stmt::Skip => sim.step(),
        Stmt::Block(stmts) => {
            for stmt_id in stmts {
                mapping(tr, st, stmt_id, sim);
            }
        }
        Stmt::Assign(lhs, rhs) => todo!(),
        Stmt::Step(_) => sim.step(),
        Stmt::Fork => todo!(),
        Stmt::While(_, _) => todo!(),
        Stmt::IfElse(_, _, _) => todo!(),
        Stmt::AssertEq(_, _) => todo!(),
    }
}

// Need to simulate protocol given a verilog file of a struct
// When given inputs, map it to expr ref

pub fn interpret(
    btor_path: &str,
    in_vals: HashMap<&str, u64>,
    out: (&str, u64),
    tr: &Transaction,
    st: &SymbolTable,
) -> bool {
    let (ctx, sys) = match patronus::btor2::parse_file(btor_path) {
        Some(result) => result,
        None => {
            println!("Failed to parse protocol file: {}", btor_path);
            return false;
        }
    };

    let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

    let mut inputs = HashMap::new();
    for (name, val) in in_vals {
        let var = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == name)
            .unwrap();
        inputs.insert(var, val);
    }

    mapping(&tr, &st, &tr.body, &mut sim);

    sim.init();

    // Fix .unwraps with ok or else and add handler
    // for (name, value) in in_vals {
    //     let var = *sys.inputs.iter().find(|i| ctx.get_symbol_name(**i).unwrap() == name).unwrap();
    //     sim.set(var, &BitVecValue::from_u64(value, 32));
    // }

    // Create functionality to simulate protocol line by line

    let out = sys.outputs;

    true
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use baa::{BitVecOps, BitVecValue};
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
    fn run_interpret() {
        let mut inputs = HashMap::new();
        inputs.insert("A", 6);
        inputs.insert("B", 7);

        let mut outputs = HashMap::new();
        outputs.insert("S", 13);
        //let success = interpret("examples/adders/add_d1.btor", inputs, outputs);
        // if success {
        //     println!("Simulation completed successfully.");
        // } else {
        //     println!("Simulation failed.");
        // }
    }

    #[test]
    #[ignore]
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

        sim.init();
        sim.set(a, &BitVecValue::from_u64(6, 32));
        sim.set(b, &BitVecValue::from_u64(7, 32));
        sim.step();
        assert_eq!(sim.get(s).unwrap().to_u64().unwrap(), 13);
    }
}
