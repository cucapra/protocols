use std::collections::hash_map::Entry;

use baa::{BitVecMutOps, BitVecOps, BitVecValue};
use log::info;
use protocols::{
    errors::{ExecutionError, ExecutionResult, SymbolError},
    interpreter::ExprValue,
    ir::{BinOp, Dir, Expr, ExprId, Stmt, StmtId, SymbolId, SymbolTable, Transaction, UnaryOp},
    scheduler::NextStmtMap,
    serialize::{serialize_args_mapping, serialize_bitvec, serialize_expr, serialize_stmt},
};
use rustc_hash::FxHashMap;

use crate::{
    global_context::GlobalContext,
    signal_trace::{PortKey, SignalTrace},
};

pub struct Interpreter {
    pub transaction: Transaction,
    pub symbol_table: SymbolTable,
    pub next_stmt_map: NextStmtMap,
    pub args_mapping: FxHashMap<SymbolId, BitVecValue>,
    pub known_bits: FxHashMap<SymbolId, BitVecValue>,

    /// The current cycle count in the trace
    /// (This field is only used to make error messages more informative)
    pub trace_cycle_count: u32,
}

impl Interpreter {
    /// Performs a context switch in the `Interpreter` by setting its
    /// `Transaction`, `SymbolTable`, `args_mapping`
    /// and `known_bits` to the specified arguments
    pub fn context_switch(
        &mut self,
        transaction: Transaction,
        symbol_table: SymbolTable,
        next_stmt_map: NextStmtMap,
        args_mapping: FxHashMap<SymbolId, BitVecValue>,
        known_bits: FxHashMap<SymbolId, BitVecValue>,
    ) {
        self.transaction = transaction;
        self.symbol_table = symbol_table;
        self.next_stmt_map = next_stmt_map;
        self.args_mapping = args_mapping;
        self.known_bits = known_bits;
    }

    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: &StmtId) -> String {
        self.transaction.format_stmt(stmt_id, &self.symbol_table)
    }

    /// Pretty-prints a `Expr` identified by its `ExprID`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_expr(&self, expr_id: &ExprId) -> String {
        self.transaction.format_expr(expr_id, &self.symbol_table)
    }

    /// Creates a new Interpreter for a given `Transaction`
    pub fn new(
        transaction: Transaction,
        symbol_table: SymbolTable,
        ctx: &GlobalContext,
        trace_cycle_count: u32,
    ) -> Self {
        let mut args_mapping = FxHashMap::default();
        let mut known_bits = FxHashMap::default();

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
            let bitwidth = current_value.width();
            args_mapping.insert(*pin_id, current_value);

            // Insert a bitstring of all `1`s into `known_bits`,
            // with length equal to the bit-width of `current_value`
            known_bits.insert(*pin_id, BitVecValue::ones(bitwidth));
        }

        info!(
            "initial args_mapping:\n{}",
            serialize_args_mapping(&args_mapping, &symbol_table, ctx.display_hex)
        );

        info!("initial known_bits:\n{:?}", known_bits);

        Self {
            transaction: transaction.clone(),
            symbol_table,
            next_stmt_map: transaction.next_stmt_mapping(),
            args_mapping,
            trace_cycle_count,
            known_bits,
        }
    }

    /// Evaluates an `Expr` identified by its `ExprId`, returning an `ExprValue`
    fn evaluate_expr(
        &mut self,
        expr_id: &ExprId,
        ctx: &GlobalContext,
    ) -> ExecutionResult<ExprValue> {
        let transaction = self.transaction.clone();
        let expr = &transaction[expr_id];
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec.clone())),
            Expr::Sym(sym_id) => {
                let name = self.symbol_table[sym_id].full_name(&self.symbol_table);

                // First check if the symbol is in args_mapping
                // (the symbol corresponds to a parameter to the transaction)
                if let Some(value) = self.args_mapping.get(sym_id) {
                    Ok(ExprValue::Concrete(value.clone()))
                }
                // Otherwise, try to fetch the value from the trace
                else if let Ok(value) = ctx.trace.get(ctx.instance_id, *sym_id) {
                    info!(
                        "Trace @ cycle {}: `{}` has value {}",
                        self.trace_cycle_count,
                        name,
                        serialize_bitvec(&value, ctx.display_hex)
                    );
                    // Check if the symbol we're referring to
                    // is the DUT pin corresponding to an output parameter

                    // Concretely, we check if the identifier begins with
                    // the name of the DUT (e.g. check if "DUT.s" begins with "DUT.")
                    let dut_prefix = format!("{}.", self.symbol_table[ctx.design.symbol_id].name());
                    if name.starts_with(&dut_prefix) {
                        let pin_name = &name[dut_prefix.len()..];

                        // Find if there's an output parameter with this name
                        // that hasn't been added to the `args_mapping` yet
                        for arg in &self.transaction.args {
                            if let Dir::Out = arg.dir() {
                                let param_name = self.symbol_table[arg.symbol()].name();
                                if param_name == pin_name
                                    && !self.args_mapping.contains_key(&arg.symbol())
                                {
                                    // If yes, we read the value for the corresponding
                                    // DUT pin from the trace, and update the args_mapping
                                    // so that `<output_param> |-> <value_of_DUT_pin_from_trace>`
                                    info!(
                                        "Capturing output parameter {} = {}",
                                        param_name,
                                        serialize_bitvec(&value, ctx.display_hex)
                                    );
                                    self.args_mapping.insert(arg.symbol(), value.clone());
                                    break;
                                }
                            }
                        }
                    }
                    Ok(ExprValue::Concrete(value))
                } else {
                    info!(
                        "args_mapping: \n{}",
                        serialize_args_mapping(
                            &self.args_mapping,
                            &self.symbol_table,
                            ctx.display_hex
                        )
                    );

                    Err(ExecutionError::symbol_not_found(
                        *sym_id,
                        name.to_string(),
                        "args_mapping or trace".to_string(),
                        *expr_id,
                    ))
                }
            }
            Expr::DontCare => Ok(ExprValue::DontCare),
            Expr::Binary(bin_op, lhs_id, rhs_id) => {
                let lhs_val = self.evaluate_expr(lhs_id, ctx)?;
                let rhs_val = self.evaluate_expr(rhs_id, ctx)?;
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
                let expr_val = self.evaluate_expr(expr_id, ctx)?;
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
                let expr_val = self.evaluate_expr(expr_id, ctx)?;
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

    /// Helper function to map an output parameter of a function (`out_param_symbol`)
    /// to the trace value for `trace_symbol`. This function checks
    /// if `trace_symbol` exists in the trace and `out_param_symbol` is
    /// currently *not* in the `args_mapping`. If so, it
    /// adds a mapping from `out_param_symbol` to the trace value.
    ///
    /// Other arguments:
    /// - `out_param_name` & `trace_symbol_name`
    ///   are the full (string) names corresponding to the two symbols
    ///   respectively.
    /// - `trace_symbol_expr_id` is the `ExprId` of `trace_symbol` (this is
    ///   only used to enable more precise error message locations)
    fn map_output_param_to_trace(
        &mut self,
        out_param_symbol: SymbolId,
        trace_symbol: SymbolId,
        out_param_name: &str,
        trace_symbol_name: &str,
        trace_symbol_expr_id: ExprId,
        ctx: &GlobalContext,
    ) -> ExecutionResult<()> {
        if let Ok(value) = ctx.trace.get(ctx.instance_id, trace_symbol) {
            // Only modify the args_mapping if `out_param_symbol`
            // is currently *not* present
            // (Clippy suggested checking if the `Entry` is `Vacant`
            // instead of using `contains_key` + `insert`)
            if let Entry::Vacant(e) = self.args_mapping.entry(out_param_symbol) {
                e.insert(value.clone());
                info!(
                    "Extended args_mapping with {} |-> {}",
                    out_param_name,
                    serialize_bitvec(&value, ctx.display_hex)
                );
                Ok(())
            } else {
                // If `out_param_symbol` is already in the `args_mapping`,
                // we do nothing (we don't want to overwrite existing
                // key-value bindings)
                Ok(())
            }
        } else {
            info!(
                "args_mapping: \n{}",
                serialize_args_mapping(&self.args_mapping, &self.symbol_table, ctx.display_hex)
            );

            Err(ExecutionError::symbol_not_found(
                trace_symbol,
                trace_symbol_name.to_string(),
                "trace".to_string(),
                trace_symbol_expr_id,
            ))
        }
    }

    /// Evaluates a `Statement` identified by its `StmtId`,
    /// returning the `StmtId` of the next statement to evaluate (if one exists)
    pub fn evaluate_stmt(
        &mut self,
        stmt_id: &StmtId,
        ctx: &GlobalContext,
    ) -> ExecutionResult<Option<StmtId>> {
        let transaction = self.transaction.clone();
        let stmt = &transaction[stmt_id];
        info!(
            "Examining statement `{}`",
            serialize_stmt(&self.transaction, &self.symbol_table, stmt_id)
        );
        match stmt {
            Stmt::Assign(symbol_id, expr_id) => {
                self.evaluate_assign(symbol_id, expr_id, ctx)?;
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                self.evaluate_if(cond_expr_id, then_stmt_id, else_stmt_id, ctx)
            }
            Stmt::While(loop_guard_id, do_block_id) => {
                self.evaluate_while(loop_guard_id, stmt_id, do_block_id, ctx)
            }
            Stmt::Step | Stmt::Fork => {
                // The scheduler handles `step`s and `fork`s.
                // Here, we simply return the next statement to run
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::AssertEq(expr_id1, expr_id2) => {
                let e1 = &self.transaction[expr_id1];
                let e2 = &self.transaction[expr_id2];
                match (e1, e2) {
                    // If the two args to `assert_eq`s are both identifiers,
                    // one of them is an output param of the transaction,
                    // & the other is a DUT output port
                    (Expr::Sym(symbol_id1), Expr::Sym(symbol_id2)) => {
                        // We deference the two `SymbolId`s in order to
                        // avoid borrow-checker issues here
                        let symbol_id1 = *symbol_id1;
                        let symbol_id2 = *symbol_id2;

                        let name1 = self.symbol_table.full_name_from_symbol_id(&symbol_id1);
                        let name2 = self.symbol_table.full_name_from_symbol_id(&symbol_id2);

                        let out_params: Vec<SymbolId> = self
                            .transaction
                            .get_parameters_by_direction(Dir::Out)
                            .collect();
                        for out_param_symbol in out_params {
                            if out_param_symbol == symbol_id1 {
                                info!("{} is an output param of the transaction", name1);
                                self.map_output_param_to_trace(
                                    symbol_id1, symbol_id2, &name1, &name2, *expr_id2, ctx,
                                )?;
                            } else if out_param_symbol == symbol_id2 {
                                info!("{} is an output param of the transaction", name2);
                                self.map_output_param_to_trace(
                                    symbol_id2, symbol_id1, &name2, &name1, *expr_id1, ctx,
                                )?;
                            }
                        }
                        Ok(self.next_stmt_map[stmt_id])
                    }
                    (_, _) => {
                        // Handle other exprs that are supplied to `assert_eq`,
                        // e.g. bit-slices
                        if self.evaluate_expr(expr_id1, ctx).is_err() {
                            info!("{} is ???", self.format_expr(expr_id1))
                        }
                        if self.evaluate_expr(expr_id2, ctx).is_err() {
                            info!("{} is ???", self.format_expr(expr_id2))
                        }
                        info!(
                            "Skipping assertion `{}` ({})",
                            self.format_stmt(stmt_id),
                            stmt_id
                        );
                        Ok(self.next_stmt_map[stmt_id])
                    }
                }
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
        ctx: &GlobalContext,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(cond_expr_id, ctx)?;
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
    /// When the monitor encounters an assignment of the form `lhs_symbol_id := rhs_expr_id`,
    /// e.g. `DUT.a := a` (where `stmt_id` is the `StmtId` of the assignment):
    /// 1. It first tries to evaluate `rhs_expr_id` to a value.
    /// 2. If `rhs_expr_id` successfully evaluates to a value, we know the corresponding
    ///    `expr` is a value.
    ///   - We compare this constant value with the value of `lhs_symbol_id` (the LHS)
    ///     (the DUT pin) from the trace.
    ///   - If the values are different, we emit a `ValueDisagreesWithTrace` error
    /// 3. If `rhs_expr_id` can't be evaluated to a value (e.g. it fails with a `SymbolNotFound` error),
    ///    this is either because `rhs_expr_id` is an unsupported expr pattern (indicated w/ `todo!(...)`)
    ///    or `rhs_expr_id` corresponds to a `Symbol` that is currently not in `args_mapping`.
    ///   - For the latter, we check if the expr is a symbol.
    ///   - If it is a symbol `s`, update `args_mapping` to be `args_mapping[s |-> read_trace(lhs_symbol_id)]`,
    ///     i.e. make the symbol `s` point to the trace value for `lhs_symbol_id`
    ///     in the resultant `args_mapping`.
    ///   - For any other expr pattern, we do `todo!(...)`
    fn evaluate_assign(
        &mut self,
        lhs_symbol_id: &SymbolId,
        rhs_expr_id: &ExprId,
        ctx: &GlobalContext,
    ) -> ExecutionResult<()> {
        let lhs = self.symbol_table.full_name_from_symbol_id(lhs_symbol_id);
        match self.evaluate_expr(rhs_expr_id, ctx) {
            Ok(ExprValue::Concrete(rhs_value)) => {
                let rhs_expr = &self.transaction[rhs_expr_id];

                // TODO: need to handle assigning to a known bit-slice

                match rhs_expr {
                    Expr::Const(_) | Expr::Sym(_) => {
                        if let Expr::Sym(_) = rhs_expr {
                            info!(
                                "`{}` evaluates to Concrete Value `{}`",
                                serialize_expr(&self.transaction, &self.symbol_table, rhs_expr_id),
                                serialize_bitvec(&rhs_value, ctx.display_hex)
                            );
                        }

                        // If the `rhs` is a constant or an identifier,
                        // we compare it with the trace's value for the LHS
                        if let Ok(trace_value) = ctx.trace.get(ctx.instance_id, *lhs_symbol_id) {
                            // If they're different, we report an error
                            if rhs_value != trace_value {
                                Err(ExecutionError::value_disagrees_with_trace(
                                    *rhs_expr_id,
                                    rhs_value,
                                    trace_value,
                                    *lhs_symbol_id, // Use LHS symbol for error reporting
                                    lhs.to_string(),
                                    self.trace_cycle_count,
                                ))
                            } else {
                                // Update the `known_bits` mapping for the RHS
                                // with all 1s (since the RHS is an input parameter
                                // whose value we are learning)
                                if let Expr::Sym(rhs_symbol_id) = rhs_expr {
                                    let width = trace_value.width();
                                    self.known_bits
                                        .insert(*rhs_symbol_id, BitVecValue::ones(width));
                                }
                                Ok(())
                            }
                        } else {
                            info!(
                                "Unable to find value for `{}` in trace at cycle {:?}",
                                lhs, self.trace_cycle_count
                            );
                            Err(ExecutionError::symbol_not_found(
                                *lhs_symbol_id,
                                lhs.to_string(),
                                "trace".to_string(),
                                *rhs_expr_id,
                            ))
                        }
                    }
                    Expr::Slice(_, _, _) => {
                        todo!("Handle case when RHS is a bit-slice that evaluates to a value")
                    }
                    _ => todo!(
                        "Unhandled expr pattern {} which evaluates to {}",
                        serialize_expr(&self.transaction, &self.symbol_table, rhs_expr_id),
                        serialize_bitvec(&rhs_value, ctx.display_hex)
                    ),
                }
            }
            Ok(ExprValue::DontCare) => Ok(()),
            Err(ExecutionError::Symbol(SymbolError::NotFound { .. })) => {
                let rhs_expr = &self.transaction[rhs_expr_id];
                match rhs_expr {
                    Expr::Sym(rhs_symbol_id) => {
                        let symbol_name =
                            self.symbol_table[rhs_symbol_id].full_name(&self.symbol_table);
                        info!(
                            "RHS of assignment is a symbol `{}` ({}) that is not in the args_mapping, adding it...",
                            symbol_name, rhs_symbol_id
                        );
                        if let Ok(trace_value) = ctx.trace.get(ctx.instance_id, *lhs_symbol_id) {
                            self.args_mapping
                                .insert(*rhs_symbol_id, trace_value.clone());

                            // All the bits are known, so we insert a bit-string of
                            // all 1s into the `known_bits` map
                            // From type-checking, we know that the bitwidth of the
                            // LHS & RHS must be the same (otherwise the type-checker
                            // would have rejected the program)
                            let width = trace_value.width();
                            self.known_bits
                                .insert(*rhs_symbol_id, BitVecValue::ones(width));

                            info!(
                                "Updated args_mapping to map {} |-> {}",
                                symbol_name,
                                serialize_bitvec(&trace_value, ctx.display_hex)
                            );
                            Ok(())
                        } else {
                            Err(ExecutionError::symbol_not_found(
                                *lhs_symbol_id,
                                symbol_name,
                                "trace".to_string(),
                                *rhs_expr_id,
                            ))
                        }
                    }
                    Expr::Slice(rhs_expr_id, msb, lsb) => {
                        let rhs_expr = &self.transaction[rhs_expr_id];
                        match rhs_expr {
                            Expr::Sym(rhs_symbol_id) => {
                                let symbol_name =
                                    self.symbol_table[rhs_symbol_id].full_name(&self.symbol_table);
                                info!(
                                    "RHS of assignment is a symbol `{}` ({}) that is not in the args_mapping, adding it...",
                                    symbol_name, rhs_symbol_id
                                );

                                // Look up the trace value corresponding
                                // to the LHS
                                if let Ok(trace_value) =
                                    ctx.trace.get(ctx.instance_id, *lhs_symbol_id)
                                {
                                    let width = trace_value.width();
                                    // Check whether the slice is valid
                                    if *msb < width && *lsb <= *msb {
                                        // Slice the value we get from the trace,
                                        // then insert it into the args_mapping
                                        let sliced_value = trace_value.slice(*msb, *lsb);
                                        self.args_mapping.insert(*rhs_symbol_id, sliced_value);

                                        // Create a `BitVecValue` `known_mask`
                                        // with the same width as `trace_value`,
                                        // where bits `[msb:lsb]` are 1,
                                        // and all other bits are 0 (this indicates
                                        // which bits are "known" from the trace)
                                        let mut known_mask = BitVecValue::zero(width);
                                        for idx in *lsb..=*msb {
                                            known_mask.set_bit(idx);
                                        }
                                        // Update `known_bits` with `rhs_symbol_id |-> known_mask`
                                        self.known_bits.insert(*rhs_symbol_id, known_mask);
                                        Ok(())
                                    } else {
                                        Err(ExecutionError::invalid_slice(
                                            *rhs_expr_id,
                                            *msb,
                                            *lsb,
                                            width,
                                        ))
                                    }
                                } else {
                                    Err(ExecutionError::symbol_not_found(
                                        *lhs_symbol_id,
                                        symbol_name,
                                        "trace".to_string(),
                                        *rhs_expr_id,
                                    ))
                                }
                            }
                            _ => {
                                // Illegal bit-slice operation
                                // (this will already have been caught by the type-checker)
                                Err(ExecutionError::arithmetic_error(
                                    "BITSLICE".to_string(),
                                    "Invalid bitslice operation".to_string(),
                                    *rhs_expr_id,
                                ))
                            }
                        }
                    }
                    _ => {
                        todo!(
                            "Unhandled expr pattern {} which results in SymbolNotFound error",
                            serialize_expr(&self.transaction, &self.symbol_table, rhs_expr_id),
                        )
                    }
                }
            }
            Err(e) => todo!("Unhandled error {}", e),
        }
    }

    /// Evaluates a `while`-loop with guard `loop_guard_id` and
    /// loop-body `do_block_id`. Note that the argument `while_id`
    /// is the `StmtId` for the `while`-loop itself.
    fn evaluate_while(
        &mut self,
        loop_guard_id: &ExprId,
        while_id: &StmtId,
        do_block_id: &StmtId,
        ctx: &GlobalContext,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(loop_guard_id, ctx)?;
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
    pub fn serialize_reconstructed_transaction(&self, ctx: &GlobalContext) -> String {
        // Print the full args_mapping for debugging
        info!(
            "Final args_mapping:\n{}",
            serialize_args_mapping(&self.args_mapping, &self.symbol_table, ctx.display_hex)
        );

        let mut args = vec![];
        // Iterates through each arg to the transaction and sees
        // what their final value in the `args_mapping` is
        for arg in &self.transaction.args {
            let symbol_id = arg.symbol();
            let name = self.symbol_table[symbol_id].full_name(&self.symbol_table);
            let value = self.args_mapping.get(&symbol_id).unwrap_or_else(|| {
                panic!(
                    "Unable to find value for {} ({}) in args_mapping, which is {{ {} }}",
                    name,
                    symbol_id,
                    serialize_args_mapping(&self.args_mapping, &self.symbol_table, ctx.display_hex)
                )
            });
            args.push(serialize_bitvec(value, ctx.display_hex));
        }
        format!("{}({})", self.transaction.name, args.join(", "))
    }
}
