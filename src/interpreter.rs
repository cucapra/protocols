// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use crate::errors::{ExecutionError, ExecutionResult};
use crate::ir::*;
use crate::scheduler::Todo;
use baa::{BitVecOps, BitVecValue};
use log::info;
use patronus::expr::ExprRef;
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::Output;
use rand::rngs::ThreadRng;
use rustc_hash::FxHashMap;

use std::collections::HashMap;

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
    sim: Interpreter,

    // TODO: can change to be secondarymaps for efficiency
    args_mapping: HashMap<SymbolId, BitVecValue>,
    input_mapping: HashMap<SymbolId, ExprRef>,
    output_mapping: HashMap<SymbolId, Output>,

    // tracks the input pins and their values
    input_vals: HashMap<SymbolId, InputValue>,

    assertions_enabled: bool,
    forks_enabled: bool,
    rng: ThreadRng,
}

impl<'a> Evaluator<'a> {
    pub fn new(
        args: HashMap<&str, BitVecValue>,
        tr: &'a Transaction,
        st: &'a SymbolTable,
        ctx: &'a patronus::expr::Context,
        sys: &'a patronus::system::TransitionSystem,
        mut sim: Interpreter,
    ) -> Self {
        // create mapping from each symbolId to corresponding BitVecValue based on input mapping
        let args_mapping = Evaluator::generate_args_mapping(st, args);

        // create mapping for each of the DUT's children symbols to the input and output mappings
        let dut = tr.type_param.unwrap();
        let dut_symbols = &st.get_children(&dut);

        let mut input_mapping = HashMap::new();
        let mut output_mapping = HashMap::new();

        for input in &sys.inputs {
            info!(
                "Input expr: {:?}, name: {:?}",
                (input),
                ctx.get_symbol_name(*input)
            );
        }

        for output in &sys.outputs {
            info!(
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

        let mut rng = rand::rng();

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
        sim.init(InitKind::Zero);

        Evaluator {
            tr,
            next_stmt_map: tr.next_stmt_mapping(),
            st,
            sim,
            args_mapping,
            input_mapping,
            output_mapping,
            input_vals,
            assertions_enabled: false,
            forks_enabled: false,
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

    pub fn enable_assertions(&mut self) {
        self.assertions_enabled = true;
    }

    pub fn disable_assertions(&mut self) {
        self.assertions_enabled = false;
    }

    pub fn assertions_enabled(&self) -> bool {
        self.assertions_enabled
    }

    pub fn enable_forks(&mut self) {
        self.forks_enabled = true;
    }

    pub fn disable_forks(&mut self) {
        self.forks_enabled = false;
    }

    pub fn forks_enabled(&self) -> bool {
        self.forks_enabled
    }

    // step the simulator
    pub fn sim_step(&mut self) {
        self.sim.step();

        // modify the input_vals to all be OldValues or DontCares
        self.input_vals = self
            .input_vals
            .iter()
            .map(|(k, v)| {
                let new_v = match v {
                    InputValue::NewValue(bvv) => InputValue::OldValue(bvv.clone()),
                    InputValue::OldValue(bvv) => InputValue::OldValue(bvv.clone()),
                    InputValue::DontCare(bvv) => {
                        InputValue::DontCare(BitVecValue::random(&mut self.rng, bvv.width()))
                    } // re-randomize DontCares
                };
                (*k, new_v)
            })
            .collect();
    }

    fn evaluate_expr(&mut self, expr_id: &ExprId) -> ExecutionResult<ExprValue> {
        let expr = &self.tr[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec.clone())),
            Expr::Sym(sym_id) => {
                let name = self.st[sym_id].name();
                if let Some(expr_ref) = self.input_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(
                        self.sim.get(*expr_ref).try_into().unwrap(),
                    ))
                } else if let Some(output) = self.output_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(
                        self.sim.get((output).expr).try_into().unwrap(),
                    ))
                } else if let Some(bvv) = self.args_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(bvv.clone()))
                } else {
                    Err(ExecutionError::symbol_not_found(
                        *sym_id,
                        name.to_string(),
                        "input, output, or args mapping".to_string(),
                        *expr_id,
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
                            Err(ExecutionError::dont_care_operation(
                                "equality".to_string(),
                                "binary expression".to_string(),
                                *expr_id,
                            ))
                        }
                        (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => {
                            if lhs.width() != rhs.width() {
                                Err(ExecutionError::arithmetic_error(
                                    "Equal".to_string(),
                                    format!(
                                        "Width mismatch in EQUAL operation: lhs width = {}, rhs width = {}",
                                        lhs.width(),
                                        rhs.width()
                                    ),
                                    *expr_id,
                                ))
                            } else if lhs == rhs {
                                Ok(ExprValue::Concrete(BitVecValue::new_true()))
                            } else {
                                Ok(ExprValue::Concrete(BitVecValue::new_false()))
                            }
                        }
                    },
                    BinOp::Concat => match (&lhs_val, &rhs_val) {
                        (ExprValue::DontCare, _) | (_, ExprValue::DontCare) => {
                            Err(ExecutionError::dont_care_operation(
                                "CONCAT".to_string(),
                                "binary expression".to_string(),
                                *expr_id,
                            ))
                        }
                        (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => {
                            if lhs.width() != rhs.width() {
                                Err(ExecutionError::arithmetic_error(
                                    "And".to_string(),
                                    format!(
                                        "Width mismatch in AND operation: lhs width = {}, rhs width = {}",
                                        lhs.width(),
                                        rhs.width()
                                    ),
                                    *expr_id,
                                ))
                            } else {
                                Ok(ExprValue::Concrete(lhs.concat(rhs)))
                            }
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
                    ExprValue::DontCare => Err(ExecutionError::dont_care_operation(
                        "unary operation".to_string(),
                        "unary expression".to_string(),
                        *expr_id,
                    )),
                }
            }
            Expr::Slice(expr_id, msb, lsb) => {
                let expr_val = self.evaluate_expr(expr_id)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => {
                        let width = bvv.width();
                        if *msb < width && *lsb <= *msb {
                            Ok(ExprValue::Concrete(bvv.slice(*msb, *lsb)))
                        } else {
                            Err(ExecutionError::invalid_slice(*expr_id, *msb, *lsb, width))
                        }
                    }
                    ExprValue::DontCare => Err(ExecutionError::dont_care_operation(
                        "slice".to_string(),
                        "slice expression".to_string(),
                        *expr_id,
                    )),
                }
            }
        }
    }

    pub fn evaluate_stmt(&mut self, stmt_id: &StmtId) -> ExecutionResult<Option<StmtId>> {
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
                if self.assertions_enabled {
                    self.evaluate_assert_eq(stmt_id, expr1, expr2)?;
                } else {
                    info!("Skipping assertion {:?} because assertions are disabled", stmt_id);
                }

                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    Ok(None)
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
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(cond_expr_id)?;
        match res {
            ExprValue::DontCare => Err(ExecutionError::invalid_condition(
                "if".to_string(),
                *cond_expr_id,
            )),
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
    ) -> ExecutionResult<()> {
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
                            // no width check needed; guaranteed to be the same
                            if !current_val.is_equal(&new_val) {
                                return Err(ExecutionError::conflicting_assignment(
                                    *symbol_id,
                                    self.st[symbol_id].name().to_string(),
                                    current_val.clone(),
                                    new_val,
                                    0,
                                    *stmt_id,
                                ));
                            }
                        }
                    }
                }
            }
        } else {
            // assuming Type Checking works, unreachable
            return Err(ExecutionError::symbol_not_found(
                *symbol_id,
                self.st[symbol_id].name().to_string(),
                "input pins".to_string(),
                *expr_id,
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
            Err(ExecutionError::read_only_assignment(
                *symbol_id,
                name.to_string(),
                "outputs".to_string(),
                *stmt_id,
            ))
        } else if self.args_mapping.contains_key(symbol_id) {
            Err(ExecutionError::read_only_assignment(
                *symbol_id,
                name.to_string(),
                "arguments".to_string(),
                *stmt_id,
            ))
        } else {
            Err(ExecutionError::symbol_not_found(
                *symbol_id,
                name.to_string(),
                "symbol mappings".to_string(),
                *expr_id,
            ))
        }
    }

    fn evaluate_while(
        &mut self,
        loop_guard_id: &ExprId,
        while_id: &StmtId,
        do_block_id: &StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(loop_guard_id)?;
        match res {
            ExprValue::DontCare => Err(ExecutionError::invalid_condition(
                "while".to_string(),
                *loop_guard_id,
            )),
            ExprValue::Concrete(bvv) => {
                if bvv.is_true() {
                    Ok(Some(*do_block_id))
                } else {
                    Ok(self.next_stmt_map[while_id])
                }
            }
        }
    }

    fn evaluate_assert_eq(
        &mut self,
        stmt_id: &StmtId,
        expr1: &ExprId,
        expr2: &ExprId,
    ) -> ExecutionResult<()> {
        let res1 = self.evaluate_expr(expr1)?;
        let res2 = self.evaluate_expr(expr2)?;
        let (bvv1, bvv2) = match (&res1, &res2) {
            (ExprValue::Concrete(bvv1), ExprValue::Concrete(bvv2)) => (bvv1, bvv2),
            _ => {
                return Err(ExecutionError::assertion_dont_care(*stmt_id));
            }
        };
        // short circuit guarantees width equality before is_equal call
        if bvv1.width() != bvv2.width() || !bvv1.is_equal(bvv2) {
            Err(ExecutionError::assertion_failed(
                *expr1,
                *expr2,
                bvv1.clone(),
                bvv2.clone(),
            ))
        } else {
            Ok(())
        }
    }
}
