use std::collections::HashMap;

use baa::{BitVecOps, BitVecValue};
use log::info;
use protocols::{
    errors::{ExecutionError, ExecutionResult},
    interpreter::ExprValue,
    ir::{BinOp, Expr, ExprId, Stmt, StmtId, SymbolId, SymbolTable, Transaction, UnaryOp},
};
use rustc_hash::FxHashMap;

use crate::{
    designs::Design,
    signal_trace::{PortKey, SignalTrace, WaveSignalTrace},
};

/// A "mini" interpreter for Protocols programs, to be used in conjunction
/// with the monitor.
/// - This is "mini" in the sense that it does not rely on Patronus/Yosys,
///   and it only supports a subset of the Protocols language so far.
#[allow(dead_code)]
#[derive(Debug)]
pub struct MiniInterpreter<'a> {
    /// The `Transaction` being interpreted
    transaction: &'a Transaction,

    /// The `SymbolTable` associated with the `Transaction`
    symbol_table: &'a SymbolTable,

    /// The waveform supplied by the user
    trace: WaveSignalTrace,

    /// The design under test
    design: &'a Design,

    /// Maps a `StmtId` to the `StmtId` of the
    /// next statement to interpret (if one exists)
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,

    /// `HashMap` mapping `SymbolId`s to their values
    args_mapping: HashMap<SymbolId, BitVecValue>,

    /// Whether to interpret `assert_eq` statements
    assertions_enabled: bool,
}

#[allow(dead_code)]
impl<'a> MiniInterpreter<'a> {
    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.transaction.format_stmt(stmt_id, self.symbol_table)
    }

    /// Creates a new `MiniInterpreter` given a `Transaction`, a `SymbolTable`
    /// and a `WaveSignalTrace`. This method also sets up the `args_mapping`
    /// accordingly based on the pins' values at the beginning of the signal trace.
    pub fn new(
        transaction: &'a Transaction,
        symbol_table: &'a SymbolTable,
        trace: WaveSignalTrace,
        design: &'a Design,
    ) -> Self {
        let mut args_mapping = HashMap::new();
        for port_key in trace.port_map.keys() {
            // We assume that there is only one `Instance` at the moment
            let PortKey {
                instance_id,
                pin_id,
            } = port_key;

            // Fetch the current value of the `pin_id`
            // (along with the name of the corresponding `Field`)
            let current_value = trace.get(*instance_id, *pin_id);
            let field_name = design
                .get_pin_name(pin_id)
                .unwrap_or_else(|| panic!("Missing pin_id {} in design.pins", pin_id));
            println!(
                "{} ({}) |-> {:#?} ",
                field_name,
                pin_id,
                current_value.clone()
            );

            // Update the `args_mapping` with the `current_value` for the `pin_id`
            args_mapping.insert(*pin_id, current_value);
        }

        Self {
            transaction,
            symbol_table,
            trace,
            design,
            next_stmt_map: transaction.next_stmt_mapping(),
            args_mapping,
            assertions_enabled: false,
        }
    }

    // Update the `args_mapping` with the `current_value` for the `pin_id`
    pub fn update_arg_value(&mut self, pin_id: SymbolId, value: BitVecValue) {
        self.args_mapping.insert(pin_id, value);
    }

    /// Evaluates an `Expr` identified by its `ExprId`, returning an `ExprValue`
    fn evaluate_expr(&self, expr_id: &ExprId) -> ExecutionResult<ExprValue> {
        let expr = &self.transaction[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec.clone())),
            Expr::Sym(sym_id) => {
                let name = self.symbol_table[sym_id].name();
                if let Some(value) = self.args_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(value.clone()))
                } else {
                    Err(ExecutionError::symbol_not_found(
                        *sym_id,
                        name.to_string(),
                        "input, output, or args mapping".to_string(),
                        *expr_id,
                    ))
                }
            }
            // TODO: figure out how we shoudl deal with `DontCare`s
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
                // TODO: figure out what to do if the `pin_id` already has a value in the environment
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
                // The top-level `run` function handles the step
                // Here we just return the next `stmt_id`
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::Fork => {
                todo!("Figure out how to handle Forks")
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
    fn evaluate_assign(
        &mut self,
        _stmt_id: &StmtId,
        symbol_id: &SymbolId,
        expr_id: &ExprId,
    ) -> ExecutionResult<()> {
        let lhs = self.symbol_table.full_name_from_symbol_id(symbol_id);
        let rhs_value = self.evaluate_expr(expr_id)?;
        info!("  Setting {} := {}", lhs, rhs_value);

        match rhs_value {
            ExprValue::Concrete(bitvec_value) => {
                self.update_arg_value(*symbol_id, bitvec_value);
            }
            // We don't need to anything for `DontCare`s at the moment
            ExprValue::DontCare => (),
        }
        Ok(())
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

    /// Evaluates an `assert_eq` statement
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

    /// Runs the `MiniInterpreter` on the Protocols file
    pub fn run(&mut self) {
        let mut current_stmt_id = self.transaction.body;
        loop {
            info!(
                "  Evaluating statement: `{}`",
                self.format_stmt(&current_stmt_id)
            );

            match self.evaluate_stmt(&current_stmt_id) {
                Ok(Some(next_stmt_id)) => match self.transaction[next_stmt_id] {
                    Stmt::Step => {
                        // trace.step() returns a `StepResult` which is either `Done` or `Ok`
                        // In either case, we can just ignore the `StepResult` and
                        // return the `StmtId` of the next statement to execute
                        let _ = self.trace.step();
                        current_stmt_id = next_stmt_id;
                    }
                    Stmt::Fork => todo!("TODO: Figure out how to handle Fork"),
                    _ => {
                        // default "just keep going" case
                        current_stmt_id = next_stmt_id;
                    }
                },

                // no more statements -> done
                Ok(None) => {
                    info!(" Execution complete, no more statements.");
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    info!("ERROR: {:?}, terminating thread", e);
                    break;
                }
            }
        }
    }
}
