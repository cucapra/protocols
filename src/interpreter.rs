use crate::{diagnostic::*, ir::*};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::ExprRef;
use patronus::sim::{Interpreter, Simulator};
use patronus::system::Output;
use rustc_hash::FxHashMap;

use crate::yosys::yosys_to_btor;
use crate::yosys::ProjectConf;
use crate::yosys::YosysEnv;

use std::collections::HashMap;
use std::path::PathBuf;

// TODO: this is relevant for proper don't care handling in the future
pub enum Value {
    BitVec(BitVecValue),
    DontCare,
}

pub struct Evaluator<'a> {
    tr: &'a Transaction,
    next_stmt_mapping: FxHashMap<StmtId, Option<StmtId>>,
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
    pub fn new(
        args: HashMap<&str, BitVecValue>,
        tr: &'a Transaction,
        st: &'a SymbolTable,
        handler: &'a mut DiagnosticHandler,
        ctx: &'a patronus::expr::Context,
        sys: &'a patronus::system::TransitionSystem,
        sim: &'a mut Interpreter<'a>,
    ) -> Self {
        // create mapping from each symbolId to corresponding BitVecValue based on input mapping
        let args_mapping = Evaluator::generate_args_mapping(st, args);

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

        // TODO: check that the Transaction DUT matches the Btor2 DUT
        // TODO: check that every item in the args mapping is a field in the Transaction

        // Initialize sim, return the transaction!
        sim.init();

        let evaluator = Evaluator {
            tr,
            next_stmt_mapping: tr.next_stmt_mapping(),
            st,
            handler,
            sim: sim,
            args_mapping,
            input_mapping,
            output_mapping,
        };
        return evaluator;
    }

    fn generate_args_mapping(
        st: &'a SymbolTable,
        args: HashMap<&str, BitVecValue>,
    ) -> HashMap<SymbolId, BitVecValue> {
        let mut args_mapping = HashMap::new();
        for (name, value) in &args {
            if let Some(symbol_id) = st.symbol_id_from_name(name) {
                args_mapping.insert(symbol_id, (*value).clone());
            } else {
                panic!("Argument {} not found in DUT symbols.", name);
            }
        }
        args_mapping
    }
    pub fn context_switch(
        &mut self,
        tr: &'a Transaction,
        st: &'a SymbolTable,
        args: HashMap<&str, BitVecValue>,
    ) {
        self.tr = tr;
        self.st = st;
        self.args_mapping = Evaluator::generate_args_mapping(self.st, args);
    }

    pub fn create_sim_context(
        verilog_path: &str,
    ) -> (patronus::expr::Context, patronus::system::TransitionSystem) {
        // Verilog --> Btor via Yosys
        let env = YosysEnv::default();
        let inp = PathBuf::from(verilog_path);
        let mut proj = ProjectConf::with_source(inp);
        let btor_file = yosys_to_btor(&env, &mut proj, None).unwrap();

        // instantiate sim from btor file
        let (ctx, sys) = match patronus::btor2::parse_file(btor_file.as_path().as_os_str()) {
            Some(result) => result,
            None => {
                panic!("Failed to parse btor file.");
            }
        };
        (ctx, sys)
    }

    // step the simulator
    pub fn sim_step(&mut self) {
        self.sim.step();
    }

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
                    Err(format!(
                        "Symbol {} not found in input or output mapping.",
                        name
                    ))
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
        let next_stmt = self.evaluate_stmt(&body_id)?;
        let mut current_stmt = next_stmt;
        while let Some(stmt_id) = current_stmt {
            current_stmt = self.evaluate_stmt(&stmt_id)?;
        }
        return Ok(());
    }

    pub fn evaluate_stmt(&mut self, stmt_id: &StmtId) -> Result<Option<StmtId>, String> {
        match &self.tr[stmt_id] {
            Stmt::Assign(symbol_id, expr_id) => {
                // println!("Eval Assign.");
                self.evaluate_assign(&symbol_id, &expr_id)?;
                Ok(self.next_stmt_mapping[stmt_id])
            }
            Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                // println!("Eval IFElse.");
                self.evaluate_if(&cond_expr_id, &then_stmt_id, &else_stmt_id)
            }
            Stmt::While(loop_guard_id, do_block_id) => {
                // println!("Eval While.");
                self.evaluate_while(&loop_guard_id, stmt_id, &do_block_id)
            }
            Stmt::Step => {
                // println!("Eval Step.");
                // self.evaluate_step()?;
                Ok(self.next_stmt_mapping[stmt_id])
            }
            Stmt::Fork => {
                // println!("Eval Fork.");
                // the scheduler will handle the fork. simple return the next statement to run
                return Ok(self.next_stmt_mapping[stmt_id]);
                // return Err("Fork not implemented.".to_string());
            }
            Stmt::AssertEq(expr1, expr2) => {
                // println!("Eval AssertEq.");
                self.evaluate_assert_eq(&expr1, &expr2)?;
                Ok(self.next_stmt_mapping[stmt_id])
            }
            Stmt::Block(stmt_ids) => {
                // println!("Eval Block.");
                if stmt_ids.is_empty() {
                    return Ok(None);
                } else {
                    return Ok(Some(stmt_ids[0]));
                }
            }
        }
    }

    fn evaluate_if(
        &mut self,
        cond_expr_id: &ExprId,
        then_stmt_id: &StmtId,
        else_stmt_id: &StmtId,
    ) -> Result<Option<StmtId>, String> {
        let res = self.evaluate_expr(cond_expr_id)?;
        if res.is_zero() {
            Ok(Some(*else_stmt_id))
        } else {
            Ok(Some(*then_stmt_id))
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

    fn evaluate_while(
        &mut self,
        loop_guard_id: &ExprId,
        while_id: &StmtId,
        do_block_id: &StmtId,
    ) -> Result<Option<StmtId>, String> {
        let res = self.evaluate_expr(loop_guard_id)?;
        if res.is_true() {
            return Ok(Some(*do_block_id));
        } else {
            Ok(self.next_stmt_mapping[while_id])
        }
    }

    fn evaluate_step(&mut self) -> Result<(), String> {
        self.sim.step();
        Ok(())
    }

    fn evaluate_fork(&self) -> Result<(), String> {
        // TODO: Implement evaluate_fork
        Ok(())
    }

    fn evaluate_assert_eq(&mut self, expr1: &ExprId, expr2: &ExprId) -> Result<(), String> {
        let res1 = self.evaluate_expr(expr1)?;
        let res2 = self.evaluate_expr(expr2)?;
        if res1.is_not_equal(&res2) {
            self.handler
                .emit_diagnostic_assertion(self.tr, expr1, expr2, &res1, &res2);
            Err("Assertion Failed".to_string())
        } else {
            Ok(())
        }
    }

    fn evaluate_block(&mut self, stmt_id: &StmtId) -> Result<Option<StmtId>, String> {
        match &self.tr[stmt_id] {
            Stmt::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    return Ok(self.next_stmt_mapping[stmt_id]);
                } else {
                    return Ok(Some(stmt_ids[0]));
                }
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

    // create evaluator
    let mut evaluator = Evaluator::new(args, tr, st, handler, &ctx, &sys, &mut sim);
    evaluator.evaluate_transaction()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::parser::parse_file;
    use core::panic;
    use insta::Settings;
    use std::path::Path;
    use strip_ansi_escapes::strip_str;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    fn test_helper(
        filename: &str,
        snap_name: &str,
        verilog_path: &str,
        args: HashMap<&str, BitVecValue>,
    ) {
        let handler = &mut DiagnosticHandler::new();

        let transaction_filename = filename;
        let verilog_path = verilog_path;
        let (ctx, sys) = Evaluator::create_sim_context(verilog_path);
        let mut sim: Interpreter<'_> = patronus::sim::Interpreter::new(&ctx, &sys);

        let trs: Vec<(SymbolTable, Transaction)> = parsing_helper(transaction_filename, handler);

        // only one transaction in this file
        let (st, tr) = &trs[0];

        let mut evaluator = Evaluator::new(args, tr, st, handler, &ctx, &sys, &mut sim);
        let res = evaluator.evaluate_transaction();

        let mut content = {
            if let Err(err) = res.clone() {
                err + "\n\n"
            } else {
                "Assertion Passed\n\n".to_string()
            }
        };

        content = content + &strip_str(handler.error_string());

        println!("{}", content);
        snap(snap_name, content);
    }

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
    fn test_add_ok() {
        // set up the args for the Transaction
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(14, 32));

        test_helper(
            "tests/add_struct.prot",
            "add_ok",
            "examples/adders/add_d1.v",
            args,
        );
    }

    #[test]
    #[ignore]
    fn test_add_err() {
        // set up the args for the Transaction
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(13, 32));

        test_helper(
            "tests/add_struct.prot",
            "add_err",
            "examples/adders/add_d1.v",
            args,
        );
    }

    #[test]
    #[ignore]
    fn test_mult_execution() {
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(6, 32));
        args.insert("b", BitVecValue::from_u64(8, 32));
        args.insert("s", BitVecValue::from_u64(48, 32));

        test_helper(
            "tests/mul.prot",
            "mult_execution",
            "examples/multipliers/mult_d2.v",
            args,
        );
    }

    #[test]
    fn test_simple_if_execution() {
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(32, 64));
        args.insert("s", BitVecValue::from_u64(7, 64));

        test_helper(
            "tests/simple_if.prot",
            "simple_if_execution",
            "examples/counter/counter.v",
            args,
        );
    }

    #[test]
    fn test_simple_while_execution() {
        let mut args = HashMap::new();
        args.insert("a", BitVecValue::from_u64(32, 64));
        args.insert("b", BitVecValue::from_u64(15, 64));
        args.insert("s", BitVecValue::from_u64(17, 64));

        test_helper(
            "tests/simple_while.prot",
            "simple_while_execution",
            "examples/counter/counter.v",
            args,
        );
    }
}
