// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::errors::{ExecutionError, ExecutionResult};
use crate::ir::*;
use crate::scheduler::Todo;
use crate::serialize::serialize_type;
use baa::{BitVecOps, BitVecValue};
use log::info;
use patronus::expr::ExprRef;
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::Output;
use rand::SeedableRng;
use rand::rngs::StdRng;
use rustc_hash::FxHashMap;

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

    /// Returns the bitwidth of an `InputValue`
    pub fn bitwidth(&self) -> u32 {
        self.value().width()
    }

    /// Creates a random `InputValue::DontCare` value with the specified `width`
    /// using the `rng` provided
    pub fn dont_care(mut rng: StdRng, width: u32) -> InputValue {
        InputValue::DontCare(BitVecValue::random(&mut rng, width))
    }
}

/// An `ExprValue` is either a `Concrete` bit-vector value, or `DontCare`
#[derive(PartialEq, Debug, Clone)]
pub enum ExprValue {
    Concrete(BitVecValue),
    DontCare,
}

/// An `Evaluator` evaluates ("interprets") a Protocols program
pub struct Evaluator<'a> {
    tr: &'a Transaction,
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,
    st: &'a SymbolTable,
    sim: Interpreter,

    args_mapping: FxHashMap<SymbolId, BitVecValue>,
    input_mapping: FxHashMap<SymbolId, ExprRef>,
    output_mapping: FxHashMap<SymbolId, Output>,

    // Combinational dependency tracking
    input_dependencies: FxHashMap<SymbolId, Vec<SymbolId>>,
    output_dependencies: FxHashMap<SymbolId, Vec<SymbolId>>,

    // tracks forbidden ports due to combinational dependencies
    forbidden_inputs: Vec<SymbolId>,
    forbidden_outputs: Vec<SymbolId>,

    // tracks the input pins and their values
    input_vals: FxHashMap<SymbolId, InputValue>,

    assertions_enabled: bool,

    /// Random number generator used for generating random values for `DontCare`
    rng: StdRng,
}

impl<'a> Evaluator<'a> {
    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.tr.format_stmt(stmt_id, self.st)
    }

    /// Creates a new `Evaluator`
    pub fn new(
        args: FxHashMap<&str, BitVecValue>,
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

        let mut input_mapping = FxHashMap::default();
        let mut output_mapping = FxHashMap::default();

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

        // For simplicity, we initialize an RNG with the seed 0 when generating
        // random values for `DontCare`s
        let mut rng = StdRng::seed_from_u64(0);

        // Initialize the input pins with DontCares that are randomly assigned
        let mut input_vals = FxHashMap::default();
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

        // Build combinational dependency graphs
        let mut output_dependencies: FxHashMap<SymbolId, Vec<SymbolId>> = FxHashMap::default();
        let mut input_dependencies: FxHashMap<SymbolId, Vec<SymbolId>> = FxHashMap::default();

        // Initialize: keys are outputs -> output_dependencies, and inputs -> input_dependencies
        for symbol_id in output_mapping.keys() {
            output_dependencies.insert(*symbol_id, Vec::new());
        }
        for symbol_id in input_mapping.keys() {
            input_dependencies.insert(*symbol_id, Vec::new());
        }

        // For each output, find all inputs in its combinational cone of influence
        for (out_sym, out) in &output_mapping {
            let input_exprs =
                patronus::system::analysis::cone_of_influence_comb(ctx, sys, out.expr);
            for input_expr in input_exprs {
                // Find the protocol symbol corresponding to this input expression
                if let Some(input_sym) = input_mapping
                    .iter()
                    .find_map(|(k, v)| if *v == input_expr { Some(*k) } else { None })
                {
                    // output_dependencies: output -> Vec<input> (inputs this output depends on)
                    if let Some(vec) = output_dependencies.get_mut(out_sym) {
                        vec.push(input_sym);
                    }
                    // input_dependencies: input -> Vec<output> (outputs this input affects)
                    if let Some(vec) = input_dependencies.get_mut(&input_sym) {
                        vec.push(*out_sym);
                    }
                }
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
            input_dependencies,
            output_dependencies,
            forbidden_inputs: Vec::new(),
            forbidden_outputs: Vec::new(),
            input_vals,
            assertions_enabled: false,
            rng,
        }
    }

    /// Creates a mapping from each symbolId to corresponding BitVecValue based on input mapping
    fn generate_args_mapping(
        st: &'a SymbolTable,
        args: FxHashMap<&str, BitVecValue>,
    ) -> FxHashMap<SymbolId, BitVecValue> {
        let mut args_mapping = FxHashMap::default();
        for (name, value) in &args {
            if let Some(symbol_id) = st.symbol_id_from_name(name) {
                args_mapping.insert(symbol_id, (*value).clone());
            } else {
                panic!("Argument {} not found in DUT symbols.", name);
            }
        }
        args_mapping
    }

    /// Performs a context switch in the `Evaluator` by setting the `Evaluator`'s
    /// `Transaction` and `SymbolTable` to that of the specified `todo`
    pub fn context_switch(&mut self, todo: Todo<'a>) {
        self.tr = todo.tr;
        self.st = todo.st;
        self.args_mapping = Evaluator::generate_args_mapping(self.st, todo.args);
        self.next_stmt_map = todo.next_stmt_map;

        // Clear forbidden ports when switching to a new context (i.e. new cycle)
        self.forbidden_inputs.clear();
        self.forbidden_outputs.clear();
    }

    pub fn input_vals(&self) -> FxHashMap<SymbolId, InputValue> {
        self.input_vals.clone()
    }

    pub fn enable_assertions(&mut self) {
        self.assertions_enabled = true;
    }

    pub fn disable_assertions(&mut self) {
        self.assertions_enabled = false;
    }

    // Steps the simulator, then modifies `input_vals` to be
    // `OldValue`s or `DontCare`s
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
                    // Check if observing this output port is forbidden
                    if self.forbidden_outputs.contains(sym_id) {
                        return Err(ExecutionError::dont_care_operation(
                            String::from("OBSERVED FORBIDDEN PORT"),
                            format!("Cannot observe output '{}' after assigning don't care to a dependent input", name),
                            *expr_id,
                        ));
                    }

                    // Observing an output port forbids assignments to its dependent inputs
                    if let Some(deps) = self.output_dependencies.get(sym_id) {
                        self.forbidden_inputs.extend(deps.iter().copied());
                    }

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
                    info!(
                        "Skipping assertion `{}` ({}) because assertions are disabled",
                        self.format_stmt(stmt_id),
                        stmt_id
                    );
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

    /// Evaluates an assignment statement `symbol_id := expr_id`, where `stmt_id`
    /// is the `StmtId` of the assignment statement
    fn evaluate_assign(
        &mut self,
        stmt_id: &StmtId,
        symbol_id: &SymbolId,
        expr_id: &ExprId,
    ) -> ExecutionResult<()> {
        // TODO: There is a lot of repeated logic here. is there a way to refactor the matches to reduce this?
        // FIXME: This should return a DontCare or a NewValue
        let expr_val = self.evaluate_expr(expr_id)?;

        // Check if assigning to this input port is forbidden
        if self.forbidden_inputs.contains(symbol_id) {
            let name = self.st[symbol_id].name();
            return Err(ExecutionError::dont_care_operation(
                String::from("ASSIGNED FORBIDDEN PORT"),
                format!("Cannot assign to input '{}' after observing a dependent output", name),
                *expr_id,
            ));
        }

        // if the symbol is currently a DontCare or OldValue, turn it into a NewValue
        // if the symbol is currently a NewValue, error out -- two threads are trying to assign to the same input
        if let Some(value) = self.input_vals.get_mut(symbol_id) {
            match value {
                InputValue::DontCare(_) => {
                    match expr_val {
                        ExprValue::DontCare => {
                            // Do nothing for DontCare
                            // (we don't want to re-randomize within a cycle because that would prevent convergence)

                            // Assigning don't care: forbid all dependent outputs
                            if let Some(deps) = self.input_dependencies.get(symbol_id) {
                                self.forbidden_outputs.extend(deps.iter().copied());
                            }
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

                        // Assigning don't care: forbid all dependent outputs
                        if let Some(deps) = self.input_dependencies.get(symbol_id) {
                            self.forbidden_outputs.extend(deps.iter().copied());
                        }
                    }
                    ExprValue::Concrete(bvv) => {
                        *value = InputValue::NewValue(bvv);
                    }
                },
                InputValue::NewValue(current_val) => {
                    match expr_val {
                        ExprValue::DontCare => {
                            // do nothing

                            // Assigning don't care: forbid all dependent outputs
                            if let Some(deps) = self.input_dependencies.get(symbol_id) {
                                self.forbidden_outputs.extend(deps.iter().copied());
                            }
                        }
                        ExprValue::Concrete(new_val) => {
                            // no width check needed; guaranteed to be the same
                            // Otherwise, if `current_val != new_value`,
                            // report a `ConflictingAssignment` error
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

    /// Resets all input pins to `DontCare` (i.e. randomizes their values)
    pub fn reset_all_input_pins(&mut self) {
        // Reset all input pins
        for (input_pin, value) in self.input_vals.iter_mut() {
            let symbol_table_entry = &self.st[input_pin];
            let symbol_name = symbol_table_entry.full_name(self.st);
            let ty = symbol_table_entry.tpe();

            if let Type::BitVec(width) = ty {
                *value = InputValue::dont_care(self.rng.clone(), width);
            } else {
                panic!(
                    "Cannot set pin {} to DontCare as its type {} is not a BitVec",
                    symbol_name,
                    serialize_type(self.st, ty)
                )
            }
        }
    }
}
