use baa::{BitVecOps, BitVecValue};
use crate::{diagnostic::*, ir::*};
use patronus::sim::{Interpreter, Simulator};

use std::collections::HashMap;

struct Evaluator<'a> {
    tr: &'a Transaction,
    st: &'a SymbolTable,
    handler: &'a mut DiagnosticHandler,
    sim: &'a mut Interpreter<'a>,
    in_vals: &'a HashMap<&'a str, u64>,
}

impl<'a> Evaluator<'a> {

    // eventually we will create a value enum that will store resultant values. for now, only integers exist
    fn evaluate_expr(&self, expr_id: &ExprId) -> BitVecValue {
        let expr = &self.tr[expr_id];
        match expr {
            // nullary
            Expr::Const(bit_vec) => {
                return bit_vec.clone();
            }
            Expr::Sym(sym_id) => {
                let name = self.st[sym_id].name();
                // FIXME: Wrong way of doing it
                // return self.sim.get([name]).unwrap();
                return BitVecValue::from_u64(self.in_vals.get(name).unwrap().clone(), 32);
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
                        return if lhs_val == rhs_val { BitVecValue::new_true() } else { BitVecValue::new_false()};
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

    fn evaluate_if(&mut self, cond_expr_id: &ExprId, then_stmt_id : &StmtId, else_stmt_id : &StmtId) {
        // TODO: Implement evaluate_if
        let res = self.evaluate_expr(cond_expr_id);
        if res.is_true() {
            self.evaluate_block(else_stmt_id);
        }
        else {
            self.evaluate_block(then_stmt_id);
        }

    }

    fn evaluate_assign(&self, assign_stmt: &Stmt) {
        // TODO: Implement evaluate_if
    }

    fn evaluate_while(&mut self, loop_guard_id : &ExprId, do_block_id : &StmtId) {
        let mut res = self.evaluate_expr(loop_guard_id);
        while (res.is_true()) {
            self.evaluate_block(do_block_id);
            res = self.evaluate_expr(loop_guard_id);
        }
    }

    fn evaluate_step(&mut self, expr: &ExprId) {
        let res = self.evaluate_expr(expr);
        let val = res.to_u64().unwrap();
        for _ in 0..val {
            self.sim.step()
        }
    }

    fn evaluate_fork(&self) {
        // TODO: Implement evaluate_fork
    }

    fn evaluate_assert_eq(&self, expr1: &ExprId, expr2: &ExprId) {
        let res1 = self.evaluate_expr(expr1);
        let res2 = self.evaluate_expr(expr2);
        if res1.is_not_equal(&res2) {
            panic!("Assertion failed: values are not equal. res1: {:?}, res2: {:?}", res1, res2)
            // self.handler.error("Assertion failed: values are not equal.");
        }
        else {
            // do nothing !
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
                            self.evaluate_assign(stmt);
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
                            self.evaluate_assert_eq(expr1_id, expr2_id);
                        }
                        Stmt::Fork => {
                            // execute expr
                            self.evaluate_fork();
                        }
                    }
                }
            }
            _ => unreachable!("Expected body to be a block statement."),
        }
    }
}

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
    for (name, val) in in_vals.clone() {
        let var = *sys
            .inputs
            .iter()
            .find(|i| ctx.get_symbol_name(**i).unwrap() == name)
            .unwrap();
        inputs.insert(var, val);
    }

    sim.init();

    let evaluator = &mut Evaluator { tr, st, handler: &mut DiagnosticHandler::new(), sim: &mut sim, in_vals: &in_vals};
    evaluator.evaluate_transaction();

    // mapping(&tr, &st, &tr.body, &mut sim);

    // sim.init();

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