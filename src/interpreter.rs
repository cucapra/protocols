use crate::{diagnostic::*, ir::*, parser::*};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::{self, ExprRef};
use patronus::sim::{Interpreter, Simulator};
use patronus::system::Output;

use crate::yosys::YosysEnv;
use crate::yosys::ProjectConf;
use crate::yosys::yosys_to_btor;

use std::path::PathBuf;
use std::collections::HashMap;

enum Value {
    BitVec(BitVecValue),
    DontCare,
}

struct Evaluator<'a> {
    tr: &'a Transaction,
    st: &'a SymbolTable,
    handler: &'a mut DiagnosticHandler,
    sim: &'a mut Interpreter<'a>,
    // can change to be secondarymaps
    args_mapping: HashMap<SymbolId, BitVecValue>, // FIXME: change to bitvecval

    // combine into port map?
    input_mapping: HashMap<SymbolId, ExprRef>,
    output_mapping: HashMap<SymbolId, Output>,
}

impl<'a> Evaluator<'a> {
    fn evaluate_expr(&mut self, expr_id: &ExprId) -> Result<BitVecValue, String> {
        let expr = &self.tr[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(bit_vec.clone()),
            Expr::Sym(sym_id) => {
                let name = self.st[sym_id].name();
                if let Some(expr_ref) = self.input_mapping.get(sym_id) {
                    Ok(self.sim.get(*expr_ref).unwrap())
                } else if let Some(output) = self.output_mapping.get(sym_id) {
                    Ok(self.sim.get((*output).expr).unwrap())
                } else if let Some(bvv) = self.args_mapping.get(sym_id) {
                    Ok(bvv.clone())
                } else {
                    self.handler.emit_diagnostic_expr(
                        self.tr,
                        expr_id,
                        "Symbol not found in input or output mapping.",
                        Level::Error,
                    );
                    Err(format!("Symbol {} not found in input or output mapping.", name))
                }
            }
            Expr::DontCare => Ok(BitVecValue::new_false()),
            Expr::Binary(bin_op, lhs_id, rhs_id) => {
                let lhs_val = self.evaluate_expr(&lhs_id)?;
                let rhs_val = self.evaluate_expr(&rhs_id)?;
                match bin_op {
                    BinOp::Equal => Ok(if lhs_val.is_equal(&rhs_val) {
                        BitVecValue::new_true()
                    } else {
                        BitVecValue::new_false()
                    }),
                    BinOp::And => Ok(lhs_val.and(&rhs_val)),
                }
            }
            Expr::Unary(unary_op, expr_id) => {
                let expr_val = self.evaluate_expr(&expr_id)?;
                match unary_op {
                    UnaryOp::Not => Ok(expr_val.not()),
                }
            }
            Expr::Slice(expr_id, idx1, idx2) => {
                let expr_val = self.evaluate_expr(&expr_id)?;
                Ok(expr_val.slice(*idx1, *idx2))
            }
        }
    }

    fn evaluate_transaction(&mut self) -> Result<(), String> {
        let body_id: StmtId = self.tr.body;
        self.evaluate_block(&body_id)
    }

    fn evaluate_if(
        &mut self,
        cond_expr_id: &ExprId,
        then_stmt_id: &StmtId,
        else_stmt_id: &StmtId,
    ) -> Result<(), String> {
        let res = self.evaluate_expr(cond_expr_id)?;
        if res.is_true() {
            self.evaluate_block(else_stmt_id)
        } else {
            self.evaluate_block(then_stmt_id)
        }
    }

    fn evaluate_assign(&mut self, symbol_id: &SymbolId, expr_id: &ExprId) -> Result<(), String> {
        let expr_val = self.evaluate_expr(expr_id)?;
        let name = self.st[symbol_id].full_name(self.st);
        if let Some(expr_ref) = self.input_mapping.get(symbol_id) {
            self.sim.set(*expr_ref, &expr_val);
            Ok(())
        } 
        // below statements should be unreachable (assuming type checking works)
        else if let Some(_) = self.output_mapping.get(symbol_id) {
            // Err(format!("Attempting to assign to output {}.", name))
            unreachable!("Attempting to assign to output {}.", name)
        } else if let Some(_) = self.args_mapping.get(symbol_id) {
            // Err(format!("Attempting to assign to argument {}.", name))
            unreachable!("Attempting to assign to argument {}.", name)
        } else {
            // Err(format!("Assigning to symbol {} not yet defined.", name))
            unreachable!("Assigning to symbol {} not yet defined.", name)
        }
    }

    fn evaluate_while(&mut self, loop_guard_id: &ExprId, do_block_id: &StmtId) -> Result<(), String> {
        let mut res = self.evaluate_expr(loop_guard_id)?;
        while res.is_true() {
            self.evaluate_block(do_block_id)?;
            res = self.evaluate_expr(loop_guard_id)?;
        }
        Ok(())
    }

    fn evaluate_step(&mut self, expr: &ExprId) -> Result<(), String> {
        let res = self.evaluate_expr(expr)?;
        let val = res.to_u64().unwrap();
        for _ in 0..val {
            self.sim.step();
        }
        Ok(())
    }

    fn evaluate_fork(&self) -> Result<(), String> {
        // TODO: Implement evaluate_fork
        Ok(())
    }

    fn evaluate_assert_eq(&mut self, expr1: &ExprId, expr2: &ExprId) -> Result<(), String> {
        let res1 = self.evaluate_expr(expr1)?;
        let res2 = self.evaluate_expr(expr2)?;
        // println!("{:?}, {:?}", res1, res2);
        if res1.is_not_equal(&res2) {
            self.handler
                .emit_diagnostic_assertion(self.tr, expr1, expr2, &res1, &res2);
            Err("Assertion Failed".to_string())
        } else {
            Ok(())
        }
    }

    fn evaluate_block(&mut self, stmt_id: &StmtId) -> Result<(), String> {
        match &self.tr[stmt_id] {
            Stmt::Block(stmt_ids) => {
                for stmt_id in stmt_ids {
                    let stmt = &self.tr[stmt_id];
                    match stmt {
                        Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                            self.evaluate_if(cond_expr_id, then_stmt_id, else_stmt_id)?;
                        }
                        Stmt::While(loop_guard_id, do_block_id) => {
                            self.evaluate_while(loop_guard_id, do_block_id)?;
                        }
                        Stmt::Assign(symbol_id, expr_id) => {
                            self.evaluate_assign(symbol_id, expr_id)?;
                        }
                        Stmt::Step(expr) => {
                            self.evaluate_step(expr)?;
                        }
                        Stmt::Block(_) => {
                            self.evaluate_block(stmt_id)?;
                        }
                        Stmt::AssertEq(expr1_id, expr2_id) => {
                            self.evaluate_assert_eq(expr1_id, expr2_id)?;
                        }
                        Stmt::Fork => {
                            self.evaluate_fork()?;
                        }
                    }
                }
                Ok(())
            }
            _ => unreachable!("Expected a block statement as input to evaluate_block."),
        }
    }
}

pub fn interpret(
    verilog_path: &str,
    args: HashMap<&str, BitVecValue>,
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> Result<(), String> {
    // Verilog --> Btor via Yosys
    let env = YosysEnv::default();
    let inp = PathBuf::from(verilog_path);
    let mut proj = ProjectConf::with_source(inp);
    let btor_file = yosys_to_btor(&env, &mut proj, None).unwrap();

    // TODO: check arguments are all there and of correct types

    // instantiate sim from btor file
    let (ctx, sys) = match patronus::btor2::parse_file(btor_file.as_path().as_os_str()) {
        Some(result) => result,
        None => {
            let msg = "Failed to parse Verilog file to Btor2.".to_string();
            handler.emit_general_message(&msg, Level::Error);
            return Err(msg);
        }
    };
    let mut sim = patronus::sim::Interpreter::new(&ctx, &sys);

    // create mapping from each symbolId to corresponding BitVecValue based on input mapping
    let mut args_mapping = HashMap::new();
    for (name, value) in &args {
        if let Some(symbol_id) = st.symbol_id_from_name(name) {
            args_mapping.insert(symbol_id, (*value).clone());
        } else {
            panic!("Argument {} not found in DUT symbols.", name);
        }
    }

    // create mapping for each of the DUT's children symbols to the input and output mappings
    let dut = tr.type_args[0];
    let dut_symbols = &st.get_children(&dut);

    let mut input_mapping = HashMap::new();
    let mut output_mapping = HashMap::new();

    for symbol_id in dut_symbols {
        let symbol_name = st[symbol_id].name();

        if let Some(input_ref) = sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == symbol_name)
        {
            input_mapping.insert(*symbol_id, *input_ref);
        }

        if let Some(output_ref) = sys
            .outputs
            .iter()
            .find(|o| ctx.get_symbol_name((**o).expr).unwrap() == symbol_name)
        {
            output_mapping.insert(*symbol_id, *output_ref);
        }
    }

    // Initialize sim, evaluate the transaction!
    sim.init();

    let evaluator = &mut Evaluator {
        tr,
        st,
        handler,
        sim: &mut sim,
        args_mapping,
        input_mapping,
        output_mapping,
    };
    evaluator.evaluate_transaction()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::yosys::*;
    use core::panic;
    use std::path::PathBuf;

    fn parsing_helper(
        transaction_filename: &str,
        handler: &mut DiagnosticHandler,
    ) -> Vec<(SymbolTable, Transaction)> {
        let result = parse_file(transaction_filename, handler);
        match result {
            Ok(success_vec) => success_vec,
            Err(_) => panic!("Failed to parse file: {}", transaction_filename),
        }
    }

    #[test]
    fn test_add_execution() {
        let handler = &mut DiagnosticHandler::new();

        // test_helper("tests/add_struct.prot", "add_struct");
        let transaction_filename = "tests/add_struct.prot";
        let btor_path = "examples/adders/add_d1.v";
        let trs = parsing_helper(transaction_filename, handler);

        // only one transaction in this file
        let (st, tr) = &trs[0];

        // set up the args for the Transaction
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(14, 32));

        // FIXME: This always returns true right now
        let res = interpret(btor_path, args, tr, st, handler);
        assert!(res.is_ok());
        // TODO: Snapshots?
    }

    #[test]
    #[ignore]
    fn test_mult_execution() {
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = "tests/mul.prot";

        // TODO: Add the btor path
        let btor_path = "examples/adders/add_d1.btor";
        let trs = parsing_helper(transaction_filename, handler);
        let (st, tr) = &trs[0];

        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(48, 32));

        let res = interpret(btor_path, args, tr, st, handler);
        assert!(res.is_ok());
    }
}
