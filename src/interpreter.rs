use crate::scheduler::Todo;
use crate::{diagnostic::*, ir::*};
use baa::{BitVecOps, BitVecValue};
use patronus::expr::ExprRef;
use patronus::sim::{Interpreter, Simulator};
use patronus::system::Output;
use rand::rngs::ThreadRng;
use rustc_hash::FxHashMap;

use std::collections::HashMap;

// TODO: this is relevant for proper don't care handling in the future
#[derive(Debug, Clone)]
pub enum InputValue {
    OldValue(BitVecValue),
    NewValue(BitVecValue),
    DontCare(BitVecValue),
}

impl PartialEq for InputValue {
    fn eq(&self, other: &Self) -> bool {
        use InputValue::*;

        match (self, other) {
            (OldValue(a), OldValue(b)) => a.is_equal(b),
            (NewValue(a), NewValue(b)) => a.is_equal(b),
            (DontCare(a), DontCare(b)) => a.is_equal(b),
            _ => false,
        }
    }
}

impl InputValue {
    pub fn value(&self) -> &BitVecValue {
        match self {
            InputValue::OldValue(bvv) => bvv,
            InputValue::NewValue(bvv) => bvv,
            InputValue::DontCare(bvv) => bvv,
        }
    }
}

#[derive(PartialEq)]
pub enum ExprValue {
    Concrete(BitVecValue),
    DontCare,
}

pub struct Evaluator<'a> {
    tr: &'a Transaction,
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,
    st: &'a SymbolTable,
    pub handler: &'a mut DiagnosticHandler,
    sim: &'a mut Interpreter<'a>,

    // TODO: can change to be secondarymaps for efficiency
    args_mapping: HashMap<SymbolId, BitVecValue>,
    input_mapping: HashMap<SymbolId, ExprRef>,
    output_mapping: HashMap<SymbolId, Output>,

    // tracks the input pins and their values
    input_vals: HashMap<SymbolId, InputValue>,

    assertions_forks_enabled: bool,
    rng: ThreadRng,
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
        let dut = tr.type_param.unwrap();
        let dut_symbols = &st.get_children(&dut);

        let mut input_mapping = HashMap::new();
        let mut output_mapping = HashMap::new();

        for input in &sys.inputs {
            println!(
                "Input expr: {:?}, name: {:?}",
                (input),
                ctx.get_symbol_name(*input)
            );
        }

        for output in &sys.outputs {
            println!(
                "Output expr: {:?}, name: {:?}",
                (output).expr,
                ctx.get_symbol_name((output).expr)
            );
        }

        for symbol_id in dut_symbols {
            let symbol_name = st[symbol_id].name();

            if let Some(input_ref) = sys
                .inputs
                .iter()
                .find(|i| ctx.get_symbol_name(**i).unwrap() == symbol_name)
            {
                input_mapping.insert(*symbol_id, *input_ref);
            } else {
                // check if the DUT symbol is an output
                let output = sys
                    .outputs
                    .iter()
                    .find(|o| ctx[o.name] == symbol_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "Failed to find output with name '{}' in system outputs",
                            symbol_name
                        )
                    });
                output_mapping.insert(*symbol_id, *output);
            }
        }

        // TODO: check that the Transaction DUT matches the Btor2 DUT
        // TODO: check that every item in the args mapping is a field in the Transaction
        let mut rng = rand::thread_rng();

        // Initialize the input pins with DontCares that are randomly assigned
        let mut input_vals = HashMap::new();
        for symbol_id in input_mapping.keys() {
            // get the width from the type of the symbol
            match st[symbol_id].tpe() {
                Type::BitVec(width) => {
                    // TODO: make this value random
                    input_vals.insert(
                        *symbol_id,
                        InputValue::DontCare(BitVecValue::random(&mut rng, width)),
                    );
                }
                _ => panic!(
                    "Expected a BitVec type for symbol {}, but found {:?}",
                    symbol_id,
                    st[symbol_id].tpe()
                ),
            }
        }

        // Initialize sim, return the transaction!
        sim.init();

        Evaluator {
            tr,
            next_stmt_map: tr.next_stmt_mapping(),
            st,
            handler,
            sim,
            args_mapping,
            input_mapping,
            output_mapping,
            input_vals,
            assertions_forks_enabled: false,
            rng,
        }
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

    pub fn context_switch(&mut self, todo: Todo<'a>) {
        self.tr = todo.tr;
        self.st = todo.st;
        self.args_mapping = Evaluator::generate_args_mapping(self.st, todo.args);
        self.next_stmt_map = todo.next_stmt_map;
    }

    pub fn input_vals(&self) -> HashMap<SymbolId, InputValue> {
        self.input_vals.clone()
    }

    pub fn enable_assertions_and_forks(&mut self) {
        self.assertions_forks_enabled = true;
    }

    pub fn disable_assertions_and_forks(&mut self) {
        self.assertions_forks_enabled = false;
    }

    pub fn assertions_forks_enabled(&self) -> bool {
        self.assertions_forks_enabled
    }

    // step the simulator
    pub fn sim_step(&mut self) {
        self.sim.step();

        // modify the input_vals to all be OldValues or DoxntCares
        self.input_vals = self
            .input_vals
            .iter()
            .map(|(k, v)| {
                let new_v = match v {
                    InputValue::NewValue(bvv) => InputValue::OldValue(bvv.clone()),
                    InputValue::OldValue(bvv) => InputValue::OldValue(bvv.clone()),
                    InputValue::DontCare(bvv) => {
                        InputValue::DontCare(BitVecValue::random(&mut self.rng, bvv.width()))
                    } // re-randomuze DontCares
                };
                (*k, new_v)
            })
            .collect();
    }

    fn evaluate_expr(&mut self, expr_id: &ExprId) -> Result<ExprValue, String> {
        let expr = &self.tr[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec.clone())),
            Expr::Sym(sym_id) => {
                let name = self.st[sym_id].name();
                if let Some(expr_ref) = self.input_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(self.sim.get(*expr_ref).unwrap()))
                } else if let Some(output) = self.output_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(self.sim.get((output).expr).unwrap()))
                } else if let Some(bvv) = self.args_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(bvv.clone()))
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
            Expr::DontCare => Ok(ExprValue::DontCare),
            Expr::Binary(bin_op, lhs_id, rhs_id) => {
                let lhs_val = self.evaluate_expr(lhs_id)?;
                let rhs_val = self.evaluate_expr(rhs_id)?;
                match bin_op {
                    BinOp::Equal => match (&lhs_val, &rhs_val) {
                        (ExprValue::DontCare, _) | (_, ExprValue::DontCare) => {
                            Err("Cannot perform equality on DontCare value".to_string())
                        }
                        (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => {
                            if lhs.is_equal(rhs) {
                                Ok(ExprValue::Concrete(BitVecValue::new_true()))
                            } else {
                                Ok(ExprValue::Concrete(BitVecValue::new_false()))
                            }
                        }
                    },
                    BinOp::And => match (&lhs_val, &rhs_val) {
                        (ExprValue::DontCare, _) | (_, ExprValue::DontCare) => {
                            Err("Cannot perform AND on DontCare value".to_string())
                        }
                        (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => {
                            Ok(ExprValue::Concrete(lhs.and(rhs)))
                        }
                    },
                }
            }
            Expr::Unary(unary_op, expr_id) => {
                let expr_val = self.evaluate_expr(expr_id)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => match unary_op {
                        UnaryOp::Not => Ok(ExprValue::Concrete(bvv.not())),
                    },
                    ExprValue::DontCare => {
                        Err("Cannot perform unary operation on DontCare.".to_string())
                    }
                }
            }
            Expr::Slice(expr_id, idx1, idx2) => {
                let expr_val = self.evaluate_expr(expr_id)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => Ok(ExprValue::Concrete(bvv.slice(*idx1, *idx2))),
                    ExprValue::DontCare => panic!("Cannot perform slice operation on DontCare."),
                }
            }
        }
    }

    pub fn evaluate_stmt(&mut self, stmt_id: &StmtId) -> Result<Option<StmtId>, String> {
        match &self.tr[stmt_id] {
            Stmt::Assign(symbol_id, expr_id) => {
                self.evaluate_assign(stmt_id, symbol_id, expr_id)?;
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                self.evaluate_if(cond_expr_id, then_stmt_id, else_stmt_id)
            }
            Stmt::While(loop_guard_id, do_block_id) => {
                self.evaluate_while(loop_guard_id, stmt_id, do_block_id)
            }
            Stmt::Step => {
                // the scheduler will handle the step. simply return the next statement to run
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::Fork => {
                // the scheduler will handle the fork. simply return the next statement to run
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::AssertEq(expr1, expr2) => {
                if self.assertions_forks_enabled {
                    self.evaluate_assert_eq(expr1, expr2)?;
                }

                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    return Ok(self.next_stmt_map[stmt_id]);
                } else {
                    Ok(Some(stmt_ids[0]))
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
        match res {
            ExprValue::DontCare => {
                Err("Cannot evaluate if condition: value is DontCare.".to_string())
            }
            ExprValue::Concrete(bvv) => {
                if bvv.is_zero() {
                    Ok(Some(*else_stmt_id))
                } else {
                    Ok(Some(*then_stmt_id))
                }
            }
        }
    }

    fn evaluate_assign(
        &mut self,
        stmt_id: &StmtId,
        symbol_id: &SymbolId,
        expr_id: &ExprId,
    ) -> Result<(), String> {
        // FIXME: This should return a DontCare or a NewValue
        let expr_val = self.evaluate_expr(expr_id)?;

        // if the symbol is currently a DontCare or OldValue, turn it into a NewValue
        // if the symbol is currently a NewValue, error out -- two threads are trying to assign to the same input
        if let Some(value) = self.input_vals.get_mut(symbol_id) {
            match value {
                InputValue::DontCare(_) => {
                    match expr_val {
                        ExprValue::DontCare => {
                            // Do nothing for DontCare
                            // (we don't want to re-randomize within a cycle because that would prevent convergence)
                        }
                        ExprValue::Concrete(bvv) => {
                            *value = InputValue::NewValue(bvv);
                        }
                    }
                }
                InputValue::OldValue(old_val) => match expr_val {
                    ExprValue::DontCare => {
                        *value = InputValue::DontCare(BitVecValue::random(
                            &mut self.rng,
                            old_val.width(),
                        ));
                    }
                    ExprValue::Concrete(bvv) => {
                        *value = InputValue::NewValue(bvv);
                    }
                },
                InputValue::NewValue(current_val) => {
                    match expr_val {
                        ExprValue::DontCare => {
                            // do nothing
                        }
                        ExprValue::Concrete(new_val) => {
                            if !current_val.is_equal(&new_val) {
                                // TODO: Can include more debug info
                                let msg = format!(
                                    "Multiple threads attempting to assign to the same input: {}",
                                    self.st[symbol_id].name()
                                );
                                self.handler.emit_diagnostic_stmt(
                                    self.tr,
                                    stmt_id,
                                    &msg,
                                    Level::Error,
                                );

                                return Err(msg);
                            }
                        }
                    }
                }
            }
        } else {
            return Err(format!(
                "Symbol {} not found in input_vals.",
                self.st[symbol_id].name()
            ));
        }

        // Assign into the underlying Patronus sim
        let name = self.st[symbol_id].full_name(self.st);
        if let Some(expr_ref) = self.input_mapping.get(symbol_id) {
            self.sim.set(*expr_ref, self.input_vals[symbol_id].value());
            Ok(())
        }
        // assuming Type Checking works, these statements are unreachable
        else if self.output_mapping.contains_key(symbol_id) {
            unreachable!("Attempting to assign to output {}.", name)
        } else if self.args_mapping.contains_key(symbol_id) {
            unreachable!("Attempting to assign to argument {}.", name)
        } else {
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
        match res {
            ExprValue::DontCare => {
                Err("Cannot evaluate while condition: value is DontCare.".to_string())
            }
            ExprValue::Concrete(bvv) => {
                if bvv.is_true() {
                    Ok(Some(*do_block_id))
                } else {
                    Ok(self.next_stmt_map[while_id])
                }
            }
        }
    }

    fn evaluate_assert_eq(&mut self, expr1: &ExprId, expr2: &ExprId) -> Result<(), String> {
        let res1 = self.evaluate_expr(expr1)?;
        let res2 = self.evaluate_expr(expr2)?;
        let (bvv1, bvv2) = match (&res1, &res2) {
            (ExprValue::Concrete(bvv1), ExprValue::Concrete(bvv2)) => (bvv1, bvv2),
            _ => {
                return Err("Assertion Failed: One or both expressions are DontCare".to_string());
            }
        };
        if !bvv1.is_equal(bvv2) {
            self.handler
                .emit_diagnostic_assertion(self.tr, expr1, expr2, bvv1, bvv2);
            Err("Assertion Failed".to_string())
        } else {
            Ok(())
        }
    }
}
