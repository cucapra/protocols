use crate::ir::*;
use baa::BitVecValue;
use patronus::sim::{Interpreter, Simulator};

use std::collections::HashMap;

fn mapping(tr: &Transaction, st: &SymbolTable, stmtid: &StmtId, sim: &mut Interpreter) {
    match &tr[stmtid] {
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
}
