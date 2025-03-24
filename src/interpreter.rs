use crate::{diagnostic::*, ir::*, parser::*};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::{self, ExprRef};
use patronus::sim::{Interpreter, Simulator};
use patronus::system::Output;

use std::collections::HashMap;

struct Evaluator<'a> {
    tr: &'a Transaction,
    st: &'a SymbolTable,
    handler: &'a mut DiagnosticHandler,
    sim: &'a mut Interpreter<'a>,
    args_mapping: HashMap<SymbolId, BitVecValue>, // FIXME: change to bitvecval
    input_mapping: HashMap<SymbolId, ExprRef>,
    output_mapping: HashMap<SymbolId, Output>,
}

impl<'a> Evaluator<'a> {
    // eventually we will create a value enum that will store resultant values. for now, only integers exist
    fn evaluate_expr(&mut self, expr_id: &ExprId) -> BitVecValue {
        let expr = &self.tr[expr_id];
        match expr {
            // nullary
            Expr::Const(bit_vec) => {
                return bit_vec.clone();
            }
            Expr::Sym(sym_id) => {
                // a symbol is either in the input mapping, the output mapping, the args mapping, or an error
                let name = self.st[sym_id].name();
                if let Some(expr_ref) = self.input_mapping.get(sym_id) {
                    return self.sim.get(*expr_ref).unwrap();
                } else if let Some(output) = self.output_mapping.get(sym_id) {
                    return self.sim.get((*output).expr).unwrap();
                } else if let Some(bvv) = self.args_mapping.get(sym_id) {
                    return bvv.clone();
                } else {
                    self.handler.emit_diagnostic_expr(
                        self.tr,
                        expr_id,
                        "Symbol not found in input or output mapping.",
                        Level::Error,
                    );
                    panic!();
                }
            }
            Expr::DontCare => {
                return BitVecValue::new_false(); // TODO: what to do with don't cares?
            }
            // unary
            Expr::Binary(bin_op, lhs_id, rhs_id) => {
                let lhs_val = self.evaluate_expr(&lhs_id);
                let rhs_val = self.evaluate_expr(&rhs_id);
                match bin_op {
                    BinOp::Equal => {
                        return if lhs_val == rhs_val {
                            BitVecValue::new_true()
                        } else {
                            BitVecValue::new_false()
                        };
                    }
                    BinOp::And => {
                        return lhs_val.and(&rhs_val);
                    }
                }
            }
            // binary
            Expr::Unary(unary_op, expr_id) => {
                let expr_val = self.evaluate_expr(&expr_id);
                match unary_op {
                    UnaryOp::Not => {
                        return expr_val.not();
                    }
                }
            }
            // Slice
            Expr::Slice(expr_id, idx1, idx2) => {
                let expr_val = self.evaluate_expr(&expr_id);
                return expr_val.slice(*idx1, *idx2);
            }
        }
    }

    fn evaluate_transaction(&mut self) {
        // extract body statement from transaction
        let body_id: StmtId = self.tr.body;
        self.evaluate_block(&body_id);
    }

    fn evaluate_if(&mut self, cond_expr_id: &ExprId, then_stmt_id: &StmtId, else_stmt_id: &StmtId) {
        // TODO: Implement evaluate_if
        let res = self.evaluate_expr(cond_expr_id);
        if res.is_true() {
            self.evaluate_block(else_stmt_id);
        } else {
            self.evaluate_block(then_stmt_id);
        }
    }

    fn evaluate_assign(&mut self, symbol_id: &SymbolId, expr_id: &ExprId) {
        let expr_val = self.evaluate_expr(expr_id);
        let name = self.st[symbol_id].full_name(self.st);
        if let Some(expr_ref) = self.input_mapping.get(symbol_id) {
            self.sim.set(*expr_ref, &expr_val);
        }
        // These should all be caught at typechecking, assuming the verilog lines up with the transaction
        // TODO: Switch to Diagnostic
        else if let Some(_) = self.output_mapping.get(symbol_id) {
            panic!("Attempting to assign to output {}.", name);
        } else if let Some(_) = self.args_mapping.get(symbol_id) {
            panic!("Attempting to assign to argument {}.", name);
        } else {
            panic!("Assigning to symbol {} not yet defined.", name);
        }
    }

    fn evaluate_while(&mut self, loop_guard_id: &ExprId, do_block_id: &StmtId) {
        let mut res = self.evaluate_expr(loop_guard_id);
        while res.is_true() {
            self.evaluate_block(do_block_id);
            res = self.evaluate_expr(loop_guard_id);
        }
    }

    fn evaluate_step(&mut self, expr: &ExprId) {
        let res = self.evaluate_expr(expr);

        // FIXME: We shouldn't narrow to u64
        let val = res.to_u64().unwrap();
        for _ in 0..val {
            self.sim.step()
        }
    }

    fn evaluate_fork(&self) {
        // TODO: Implement evaluate_fork
    }

    fn evaluate_assert_eq(&mut self, expr1: &ExprId, expr2: &ExprId) -> bool {
        let res1 = self.evaluate_expr(expr1);
        let res2 = self.evaluate_expr(expr2);
        println!("{:?}, {:?}", res1, res2);
        if res1.is_not_equal(&res2) {
            self.handler
                .emit_diagnostic_assertion(self.tr, expr1, expr2, &res1, &res2);
            // panic!(
            //     "Assertion failed: values are not equal. res1: {:?}, res2: {:?}",
            //     res1, res2
            // );
            return true;
        } else {
            return false;
        }
    }

    fn evaluate_block(&mut self, stmt_id: &StmtId) {
        match &self.tr[stmt_id] {
            Stmt::Block(stmt_ids) => {
                for stmt_id in stmt_ids {
                    let stmt = &self.tr[stmt_id];
                    match stmt {
                        Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                            // execute if
                            self.evaluate_if(cond_expr_id, then_stmt_id, else_stmt_id);
                        }
                        Stmt::While(loop_guard_id, do_block_id) => {
                            // execute while
                            self.evaluate_while(loop_guard_id, do_block_id);
                        }
                        Stmt::Assign(symbol_id, expr_id) => {
                            // execute return
                            self.evaluate_assign(symbol_id, expr_id);
                        }
                        Stmt::Step(expr) => {
                            // execute expr
                            self.evaluate_step(expr);
                        }
                        Stmt::Block(_) => {
                            // execute block
                            self.evaluate_block(stmt_id);
                        }
                        Stmt::AssertEq(expr1_id, expr2_id) => {
                            // execute assert
                            let res = self.evaluate_assert_eq(expr1_id, expr2_id);
                            if !res {
                                // TODO: actually pause interpreting immediately if this occurs
                                return;
                            }
                        }
                        Stmt::Fork => {
                            // execute expr
                            self.evaluate_fork();
                        }
                    }
                }
            }
            _ => unreachable!("Expected a block statement as input to evaluate_block."),
        }
    }
}

pub fn interpret(
    btor_path: &str,
    args: HashMap<&str, BitVecValue>,
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> bool {
    // instantiate sim from btor file
    let (ctx, sys) = match patronus::btor2::parse_file(btor_path) {
        Some(result) => result,
        None => {
            println!("Failed to parse protocol file: {}", btor_path);
            return false;
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
    evaluator.evaluate_transaction();

    // let mut inputs = HashMap::new();
    // for (name, val) in args.clone() {
    //     let var = *sys
    //         .inputs
    //         .iter()
    //         .find(|i| ctx.get_symbol_name(**i).unwrap() == name)
    //         .unwrap();
    //     inputs.insert(var, val);
    // }

    // for (symbol_id, expr_ref) in &input_mapping {
    //     if let Some(value) = args_mapping.get(symbol_id) {
    //         sim.set(*expr_ref, value);
    //     } else {
    //         let name = st[symbol_id].name();
    //         panic!("Input {} not found in provided arguments.", name);
    //     }
    // }

    // let out = sys.outputs;
    // println!("{:?}", out);
    true
}

#[cfg(test)]
pub mod tests {
    use core::panic;

    use super::*;

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
        let btor_path = "examples/adders/add_d1.btor";
        let trs = parsing_helper(transaction_filename, handler);

        // only one transaction in this file
        let (st, tr) = &trs[0];

        // set up the args for the Transaction
        // FIXME: returned values from sim seem to have width 32
        // These args must also be 32-bit then, else Rust panics on comparison
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(14, 32));

        // FIXME: This always returns true right now
        let success = interpret(btor_path, args, tr, st, handler);
        assert!(success);

        // TODO: Snapshots?
    }

    #[test]
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

        let success = interpret(btor_path, args, tr, st, handler);
        assert!(success);
    }
}
