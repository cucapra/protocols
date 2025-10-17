use std::collections::HashMap;

use baa::{BitVecOps, BitVecValue};
use log::info;
use protocols::{
    errors::{ExecutionError, ExecutionResult},
    interpreter::ExprValue,
    ir::{BinOp, Expr, ExprId, Stmt, StmtId, SymbolId, SymbolTable, Transaction, UnaryOp},
    serialize::{serialize_args_mapping, serialize_bitvec},
};
use rustc_hash::FxHashMap;

use crate::{
    global_context::GlobalContext,
    signal_trace::{PortKey, SignalTrace},
};

/// The local context associated with an individual thread,
/// storing information such as:
// - Which transaction are we currently running?
// - Where in the transaction are we currently at? (the `StmtId`)
// - A mutable map mapping variable names to their values (`args_mapping`)
#[allow(dead_code)]
struct Thread<'a> {
    // The thread's ID
    thread_id: usize,

    /// The `Transaction` being interpreted
    transaction: &'a Transaction,

    /// The `SymbolTable` associated with the `Transaction`
    symbol_table: &'a SymbolTable,

    /// The current statement in the `Transaction`, identified by its `StmtId`
    stmt_id: StmtId,

    /// Maps a `StmtId` to the `StmtId` of the
    /// next statement to interpret (if one exists)
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,

    /// `HashMap` mapping `SymbolId`s to their values
    args_mapping: HashMap<SymbolId, BitVecValue>,

    /// A reference to the `GlobalContext` for all threads
    ctx: &'a GlobalContext<'a>,
}

impl<'a> Thread<'a> {
    /// Creates a new `Thread` given a `Transaction`, `SymbolTable`,
    /// `GlobalContext` and `thread_id`. This method also sets up the `args_mapping`
    /// accordingly based on the pins' values at the beginning of the signal trace.
    pub fn new(
        transaction: &'a Transaction,
        symbol_table: &'a SymbolTable,
        ctx: &'a GlobalContext,
        thread_id: usize,
    ) -> Self {
        let mut args_mapping = HashMap::new();

        for port_key in ctx.trace.port_map.keys() {
            // We assume that there is only one `Instance` at the moment
            let PortKey {
                instance_id,
                pin_id,
            } = port_key;

            // Fetch the current value of the `pin_id`
            // (along with the name of the corresponding `Field`)
            let current_value = ctx.trace.get(*instance_id, *pin_id).unwrap_or_else(|err| {
                panic!(
                    "Unable to get value for pin {pin_id} in signal trace, {:?}",
                    err
                )
            });
            args_mapping.insert(*pin_id, current_value);
        }

        Self {
            thread_id,
            transaction,
            symbol_table,
            stmt_id: transaction.body,
            next_stmt_map: transaction.next_stmt_mapping(),
            args_mapping,
            ctx,
        }
    }

    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.transaction.format_stmt(stmt_id, self.symbol_table)
    }

    /// Pretty-prints a `Expr` identified by its `ExprID`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_expr(&self, expr_id: &ExprId) -> String {
        self.transaction.format_expr(expr_id, self.symbol_table)
    }

    // Update the `args_mapping` with the `current_value` for the `pin_id`
    pub fn update_arg_value(&mut self, pin_id: SymbolId, value: BitVecValue) {
        self.args_mapping.insert(pin_id, value);
    }

    /// Evaluates an `Expr` identified by its `ExprId`, returning an `ExprValue`
    fn evaluate_expr(&mut self, expr_id: &ExprId) -> ExecutionResult<ExprValue> {
        let expr = &self.transaction[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec.clone())),
            Expr::Sym(sym_id) => {
                let name = self.symbol_table[sym_id].full_name(self.symbol_table);

                // Fetch the value for the `sym_id` from the trace,
                // then update the `args_mapping`
                if let Ok(value) = self.ctx.trace.get(self.ctx.instance_id, *sym_id) {
                    info!(
                        "In the trace, {name} has value {}",
                        serialize_bitvec(&value, self.ctx.display_hex)
                    );
                    self.update_arg_value(*sym_id, value.clone());
                    Ok(ExprValue::Concrete(value))
                } else {
                    info!(
                        "args_mapping: \n{}",
                        serialize_args_mapping(
                            &self.args_mapping,
                            self.symbol_table,
                            self.ctx.display_hex
                        )
                    );

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

    /// Evaluates a `Statement` identified by its `StmtId`,
    /// returning the `StmtId` of the next statement to evaluate (if one exists)
    pub fn evaluate_stmt(&mut self, stmt_id: &StmtId) -> ExecutionResult<Option<StmtId>> {
        match &self.transaction[stmt_id] {
            Stmt::Assign(symbol_id, expr_id) => {
                // TODO: figure out what to do if the `symbol_id` already has a value in the environment
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
                // Actual stepping is done in the `run` function below.
                // Here, we simply return the next statement to run
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::Fork => {
                todo!("Figure out how to handle Forks")
            }
            Stmt::AssertEq(expr1, expr2) => {
                if self.evaluate_expr(expr1).is_err() {
                    info!("{} is ???", self.format_expr(expr1))
                }
                if self.evaluate_expr(expr2).is_err() {
                    info!("{} is ???", self.format_expr(expr2))
                }
                info!(
                    "Skipping assertion `{}` ({}) because assertions are disabled",
                    self.format_stmt(stmt_id),
                    stmt_id
                );
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

    /// Evaluates an `if`-statement, returning the `StmtId` of the next
    /// statement to evaluate (if one exists)
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
    /// Note: most of the logic for fixed-point iteration is in
    /// `evaluate_assign` in `interpreter.rs`, we may want to
    /// look at that function to take inspiration
    fn evaluate_assign(
        &mut self,
        _stmt_id: &StmtId,
        symbol_id: &SymbolId,
        expr_id: &ExprId,
    ) -> ExecutionResult<()> {
        let lhs = self.symbol_table.full_name_from_symbol_id(symbol_id);
        let rhs_value = self.evaluate_expr(expr_id)?;

        match rhs_value.clone() {
            ExprValue::Concrete(bitvec_value) => {
                info!(
                    "Setting {} := {}",
                    lhs,
                    serialize_bitvec(&bitvec_value, self.ctx.display_hex)
                );
                self.update_arg_value(*symbol_id, bitvec_value);
            }
            ExprValue::DontCare => (),
        }
        Ok(())
    }

    /// Evaluates a `while`-loop with guard `loop_guard_id` and
    /// loop-body `do_block_id`. Note that the argument `while_id`
    /// is the `StmtId` for the `while`-loop itself.
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

    /// Prints the reconstructed transaction
    /// (i.e. the function call that led to the signal trace)
    /// Note: this function is only called at the end of `MiniInterpreter::run`
    /// after we have finished interpreting the protocol / signal trace
    fn serialize_reconstructed_transaction(&self) -> String {
        let mut args = vec![];
        // Iterates through each arg to the transaction and sees
        // what their final value in the `args_mapping` is
        for arg in &self.transaction.args {
            let symbol_id = arg.symbol();
            let name = self.symbol_table[symbol_id].name();
            let value = self.args_mapping.get(&symbol_id).unwrap_or_else(|| {
                panic!(
                    "Unable to find value for {} ({}) in args_mapping",
                    name, symbol_id
                )
            });
            args.push(serialize_bitvec(value, self.ctx.display_hex));
        }
        format!("{}({})", self.transaction.name, args.join(", "))
    }
}
