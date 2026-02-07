use std::collections::hash_map::Entry;

use baa::{BitVecMutOps, BitVecOps, BitVecValue};
use log::info;
use protocols::{
    errors::{AssertionError, EvaluationError, ExecutionError, ExecutionResult, SymbolError},
    interpreter::ExprValue,
    ir::{BinOp, Dir, Expr, ExprId, Stmt, StmtId, SymbolId, SymbolTable, Transaction, UnaryOp},
    scheduler::NextStmtMap,
    serialize::{serialize_args_mapping, serialize_bitvec, serialize_expr, serialize_stmt},
};
use rustc_hash::FxHashMap;

use crate::{
    global_context::GlobalContext,
    signal_trace::{PortKey, SignalTrace, WaveSignalTrace},
    thread::Thread,
};

pub struct Interpreter {
    pub transaction: Transaction,
    pub symbol_table: SymbolTable,
    pub next_stmt_map: NextStmtMap,
    pub args_mapping: FxHashMap<SymbolId, BitVecValue>,
    pub known_bits: FxHashMap<SymbolId, BitVecValue>,

    /// Constraints on DUT input port values that must hold after stepping.
    /// These are established by assignments like `D.m_axis_tvalid := 1'b1`
    /// and verified after each `step()` to ensure the constraint still holds.
    pub constraints: FxHashMap<SymbolId, BitVecValue>,

    // Maps function parameters to DUT pins
    pub args_to_pins: FxHashMap<SymbolId, SymbolId>,

    /// The current cycle count in the trace
    /// (This field is only used to make error messages more informative)
    pub trace_cycle_count: u32,

    /// The SymbolId of the DUT (design under test)
    pub dut_symbol_id: SymbolId,
}

impl Interpreter {
    /// Performs a context switch in the `Interpreter` by setting its
    /// `Transaction`, `SymbolTable`, `args_mapping`, `known_bits`, and `constraints`
    /// to the specified arguments
    pub fn context_switch(&mut self, thread: &Thread) {
        self.transaction = thread.transaction.clone();
        self.symbol_table = thread.symbol_table.clone();
        self.next_stmt_map = thread.next_stmt_map.clone();
        self.args_mapping = thread.args_mapping.clone();
        self.known_bits = thread.known_bits.clone();
        self.constraints = thread.constraints.clone();
        self.args_to_pins = thread.args_to_pins.clone();
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
        trace: &WaveSignalTrace,
        trace_cycle_count: u32,
        dut_symbol_id: SymbolId,
    ) -> Self {
        let mut args_mapping = FxHashMap::default();
        let mut known_bits = FxHashMap::default();

        for port_key in trace.port_map.keys() {
            // We assume that there is only one `Instance` at the moment
            let PortKey {
                instance_id,
                pin_id,
            } = port_key;

            // Fetch the current value of the `pin_id`
            // (along with the name of the corresponding `Field`)
            let current_value = trace.get(*instance_id, *pin_id).unwrap_or_else(|err| {
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
            known_bits,
            constraints: FxHashMap::default(),
            trace_cycle_count,
            args_to_pins: FxHashMap::default(),
            dut_symbol_id,
        }
    }

    /// Evaluates an `Expr` identified by its `ExprId`, returning an `ExprValue`
    fn evaluate_expr(
        &mut self,
        expr_id: &ExprId,
        ctx: &GlobalContext,
        trace: &WaveSignalTrace,
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
                else if let Ok(value) = trace.get(ctx.instance_id, *sym_id) {
                    if ctx.show_waveform_time {
                        info!(
                            "Trace @ time {}: `{}` has value {}",
                            trace.format_time(trace.time_step(), ctx.time_unit),
                            name,
                            serialize_bitvec(&value, ctx.display_hex)
                        );
                    } else {
                        info!(
                            "Trace @ cycle {}: `{}` has value {}",
                            self.trace_cycle_count,
                            name,
                            serialize_bitvec(&value, ctx.display_hex)
                        );
                    }
                    // Check if the symbol we're referring to
                    // is the DUT pin corresponding to an output parameter

                    // Concretely, we check if the identifier begins with
                    // the name of the DUT (e.g. check if "DUT.s" begins with "DUT.")
                    let dut_prefix = format!("{}.", self.symbol_table[self.dut_symbol_id].name());
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
                let lhs_val = self.evaluate_expr(lhs_id, ctx, trace)?;
                let rhs_val = self.evaluate_expr(rhs_id, ctx, trace)?;
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
                                    "Concat".to_string(),
                                    format!(
                                        "Width mismatch in CONCAT operation: lhs width = {}, rhs width = {}",
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
                let expr_val = self.evaluate_expr(expr_id, ctx, trace)?;
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
            Expr::Slice(sliced_expr_id, msb, lsb) => {
                let sliced_expr = &self.transaction[sliced_expr_id];

                // Before evaluating the slice, we first need to
                // check whether all bits in the slice are currently known
                // (i.e. are set to 1 in `self.known_bits`)
                // Note: we only do this for the function's (output) parameters
                // (i.e. if `sliced_symbol_id` has *no* parent in the `SymbolTable`)
                // We don't do this for DUT (output) ports, since if they are
                // mentioned in `assert_eq`, we can just read them from the trace
                if let Expr::Sym(sliced_symbol_id) = sliced_expr {
                    if self.symbol_table[sliced_symbol_id].parent().is_none() {
                        let symbol_name = self.symbol_table[sliced_symbol_id].name();

                        // Check whether `[msb:lsb]` are all 1s in the
                        // known-bits map
                        if let Some(known_bits) = self.known_bits.get(sliced_symbol_id) {
                            let all_bits_known_in_slice =
                                (*lsb..=*msb).all(|idx| known_bits.is_bit_set(idx));
                            if !all_bits_known_in_slice {
                                // Some bits in the slice are not known yet,
                                // so we report an error
                                return Err(ExecutionError::symbol_not_found(
                                    *sliced_symbol_id,
                                    symbol_name.to_string(),
                                    format!(
                                        "known_bits (some bits in slice {}[{}:{}] are not yet known)",
                                        symbol_name, msb, lsb
                                    ),
                                    *sliced_expr_id,
                                ));
                            }
                        } else {
                            // Report an error since we are trying to slice
                            // a `symbol_id` where the provenance of the bits
                            // is unknown (i.e. it is absent from `self.known_bits`)
                            return Err(ExecutionError::symbol_not_found(
                                *sliced_symbol_id,
                                symbol_name.to_string(),
                                "known_bits".to_string(),
                                *sliced_expr_id,
                            ));
                        }
                    }
                } else {
                    return Err(ExecutionError::illegal_slice(*sliced_expr_id, *msb, *lsb));
                }

                let expr_val = self.evaluate_expr(sliced_expr_id, ctx, trace)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => {
                        let width = bvv.width();
                        // Check whether `msb` & `lsb` are in bounds
                        if *msb < width && *lsb <= *msb {
                            Ok(ExprValue::Concrete(bvv.slice(*msb, *lsb)))
                        } else {
                            Err(ExecutionError::invalid_slice(
                                *sliced_expr_id,
                                *msb,
                                *lsb,
                                width,
                            ))
                        }
                    }
                    ExprValue::DontCare => Err(ExecutionError::dont_care_operation(
                        "slice".to_string(),
                        "slice expression".to_string(),
                        *sliced_expr_id,
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
        trace_symbol_expr_id: ExprId,
        ctx: &GlobalContext,
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<()> {
        if let Ok(value) = trace.get(ctx.instance_id, trace_symbol) {
            // Only modify the args_mapping if `out_param_symbol`
            // is currently *not* present
            // (Clippy suggested checking if the `Entry` is `Vacant`
            // instead of using `contains_key` + `insert`)
            if let Entry::Vacant(e) = self.args_mapping.entry(out_param_symbol) {
                e.insert(value.clone());
                let out_param_name = self
                    .symbol_table
                    .full_name_from_symbol_id(&out_param_symbol);
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

            let trace_symbol_name = self.symbol_table.full_name_from_symbol_id(&trace_symbol);
            Err(ExecutionError::symbol_not_found(
                trace_symbol,
                trace_symbol_name,
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
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<Option<StmtId>> {
        let transaction = self.transaction.clone();
        let stmt = &transaction[stmt_id];
        info!(
            "Examining statement `{}` ({})",
            serialize_stmt(&self.transaction, &self.symbol_table, stmt_id),
            stmt_id
        );
        match stmt {
            Stmt::Assign(symbol_id, expr_id) => {
                self.evaluate_assign(symbol_id, expr_id, ctx, trace)?;
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                self.evaluate_if(cond_expr_id, then_stmt_id, else_stmt_id, ctx, trace)
            }
            Stmt::While(loop_guard_id, do_block_id) => {
                self.evaluate_while(loop_guard_id, stmt_id, do_block_id, ctx, trace)
            }
            Stmt::BoundedLoop(_, _) => {
                todo!("Bounded loops is not yet implemented in the monitor")
            }
            Stmt::Step | Stmt::Fork => {
                // The scheduler handles `step`s and `fork`s.
                // Here, we simply return the next statement to run
                Ok(self.next_stmt_map[stmt_id])
            }
            Stmt::AssertEq(expr_id1, expr_id2) => {
                self.evaluate_assert_eq(stmt_id, expr_id1, expr_id2, ctx, trace)
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

    /// Evaluates an `assert_eq` statement identified by `stmt_id`,
    /// where `expr_id1` & `expr_id2` refer to the two arguments (expressions)
    /// supplied to `assert_eq`
    fn evaluate_assert_eq(
        &mut self,
        stmt_id: &StmtId,
        expr_id1: &ExprId,
        expr_id2: &ExprId,
        ctx: &GlobalContext,
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<Option<StmtId>> {
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
                            symbol_id1, symbol_id2, *expr_id2, ctx, trace,
                        )?;
                    } else if out_param_symbol == symbol_id2 {
                        info!("{} is an output param of the transaction", name2);
                        self.map_output_param_to_trace(
                            symbol_id2, symbol_id1, *expr_id1, ctx, trace,
                        )?;
                    }
                }
                Ok(self.next_stmt_map[stmt_id])
            }
            (_, _) => {
                // Handle other exprs that are supplied to `assert_eq`
                // e.g. bit-slices

                let eval_result1 = self.evaluate_expr(expr_id1, ctx, trace);
                let eval_result2 = self.evaluate_expr(expr_id2, ctx, trace);

                match (eval_result1.clone(), eval_result2.clone()) {
                    (
                        Ok(ExprValue::Concrete(value1)),
                        Err(ExecutionError::Symbol(SymbolError::NotFound { .. })),
                    ) => {
                        self.infer_value_from_assertion(expr_id2, expr_id1, &value1, ctx)?;
                        Ok(self.next_stmt_map[stmt_id])
                    }
                    (
                        Err(ExecutionError::Symbol(SymbolError::NotFound { .. })),
                        Ok(ExprValue::Concrete(value2)),
                    ) => {
                        self.infer_value_from_assertion(expr_id1, expr_id2, &value2, ctx)?;
                        Ok(self.next_stmt_map[stmt_id])
                    }
                    // Check whether the two arguments to the assertion are equal
                    (Ok(ExprValue::Concrete(value1)), Ok(ExprValue::Concrete(value2))) => {
                        if value1 != value2 {
                            info!(
                                "Assertion `{}` failed: {} != {}",
                                self.format_stmt(stmt_id),
                                serialize_bitvec(&value1, ctx.display_hex),
                                serialize_bitvec(&value2, ctx.display_hex),
                            );
                            Err(ExecutionError::Assertion(AssertionError::EqualityFailed {
                                expr1_id: *expr_id1,
                                expr2_id: *expr_id2,
                                value1,
                                value2,
                            }))
                        } else {
                            info!("Assertion `{}` passed", self.format_stmt(stmt_id),);
                            Ok(self.next_stmt_map[stmt_id])
                        }
                    }

                    // For other cases, we skip the assertion for now
                    (Ok(_), Ok(_)) => {
                        info!(
                            "Skipping assertion `{}` ({})",
                            self.format_stmt(stmt_id),
                            stmt_id
                        );
                        Ok(self.next_stmt_map[stmt_id])
                    }
                    _ => {
                        if eval_result1.is_err() {
                            info!("{} is ???", self.format_expr(expr_id1))
                        }
                        if eval_result2.is_err() {
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
        }
    }

    /// Infers the value of an unknown expression from an assertion,
    /// and inserts a binding for it into the `args_mapping`.
    /// - `unknown_expr_id` is the expr whose value we're inferring
    /// - `known_expr_id` is the (known) expr with value `known_value`
    fn infer_value_from_assertion(
        &mut self,
        unknown_expr_id: &ExprId,
        known_expr_id: &ExprId,
        known_value: &BitVecValue,
        ctx: &GlobalContext,
    ) -> ExecutionResult<()> {
        let unknown_expr = &self.transaction[unknown_expr_id];

        match unknown_expr {
            Expr::Slice(sliced_expr_id, msb, lsb) => {
                let sliced_expr = &self.transaction[sliced_expr_id];
                match sliced_expr {
                    Expr::Sym(sliced_symbol_id) => {
                        let symbol_name =
                            self.symbol_table[sliced_symbol_id].full_name(&self.symbol_table);
                        info!(
                            "Inferring value for `{}[{}:{}]` from assertion with `{}`",
                            symbol_name,
                            msb,
                            lsb,
                            self.format_expr(known_expr_id)
                        );

                        // Check if `symbol_name` is an output parameter
                        let out_params: Vec<SymbolId> = self
                            .transaction
                            .get_parameters_by_direction(Dir::Out)
                            .collect();
                        if !out_params.contains(sliced_symbol_id) {
                            Ok(())
                        } else {
                            // Get the expected width from the symbol's type
                            let expected_width =
                                self.symbol_table[sliced_symbol_id].tpe().bitwidth();

                            // If `sliced_symbol_id` isn't in either of
                            // `args_mapping` or `known_bits`, map it to the
                            // bit-vector of all zeroes
                            self.args_mapping
                                .entry(*sliced_symbol_id)
                                .or_insert_with(|| BitVecValue::zero(expected_width));
                            self.known_bits
                                .entry(*sliced_symbol_id)
                                .or_insert_with(|| BitVecValue::zero(expected_width));

                            // Get the current value and known_bits
                            let mut current_value = self.args_mapping[sliced_symbol_id].clone();
                            let mut known_bits = self.known_bits[sliced_symbol_id].clone();

                            // Update bits `[msb:lsb]` w/ the known value
                            for i in 0..=(msb - lsb) {
                                let bit_pos = lsb + i;
                                if known_value.is_bit_set(i) {
                                    current_value.set_bit(bit_pos);
                                } else {
                                    current_value.clear_bit(bit_pos);
                                }
                                // Mark this bit as known
                                known_bits.set_bit(bit_pos);
                            }

                            // Update `args_mapping` and `known_bits` to point
                            // to the updated values & known bits
                            self.args_mapping
                                .insert(*sliced_symbol_id, current_value.clone());
                            self.known_bits
                                .insert(*sliced_symbol_id, known_bits.clone());

                            info!(
                                "Updated args_mapping: {} |-> {} (0b{})",
                                symbol_name,
                                serialize_bitvec(&current_value, ctx.display_hex),
                                current_value.to_bit_str()
                            );
                            info!(
                                "Updated known_bits: {} |-> {}",
                                symbol_name,
                                known_bits.to_bit_str()
                            );

                            Ok(())
                        }
                    }
                    _ => Ok(()),
                }
            }
            Expr::Sym(symbol_id) => {
                // Fetch all the output parameters of the function
                let out_params: Vec<SymbolId> = self
                    .transaction
                    .get_parameters_by_direction(Dir::Out)
                    .collect();

                let out_param_strs = out_params
                    .iter()
                    .map(|symbol_id| self.symbol_table[symbol_id].name().to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                info!("out_params = {}", out_param_strs);

                // If `symbol_id` is an output parameter that is currently
                // absent from `args_mapping`, insert the binding
                // `symbol_id |-> known_value` into `args_mapping`,
                // and update `known_bits` to be all ones
                if out_params.contains(symbol_id) {
                    let symbol_name = self.symbol_table[symbol_id].full_name(&self.symbol_table);

                    info!("Identified {} as an output parameter", symbol_name);

                    if let Entry::Vacant(e) = self.args_mapping.entry(*symbol_id) {
                        e.insert(known_value.clone());
                        let width = known_value.width();
                        self.known_bits.insert(*symbol_id, BitVecValue::ones(width));
                        info!(
                            "Extended args_mapping with {} |-> {}",
                            symbol_name,
                            serialize_bitvec(known_value, ctx.display_hex)
                        );
                    }
                }
                Ok(())
            }
            _ => Ok(()),
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
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(cond_expr_id, ctx, trace)?;
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
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<()> {
        let lhs_name = self.symbol_table.full_name_from_symbol_id(lhs_symbol_id);
        match self.evaluate_expr(rhs_expr_id, ctx, trace) {
            Ok(ExprValue::Concrete(rhs_value)) => {
                let rhs_expr = &self.transaction[rhs_expr_id];
                match rhs_expr {
                    Expr::Const(_) | Expr::Sym(_) => {
                        // We only print out the following log for the case
                        // where a variable evaluates to a value, since the
                        // constant case is trivial
                        if let Expr::Sym(_) = rhs_expr {
                            info!(
                                "`{}` evaluates to Concrete Value `{}`",
                                serialize_expr(&self.transaction, &self.symbol_table, rhs_expr_id),
                                serialize_bitvec(&rhs_value, ctx.display_hex)
                            );
                        }

                        // If the `rhs` is a constant or an identifier,
                        // we compare it with the trace's value for the LHS
                        if let Ok(trace_value) = trace.get(ctx.instance_id, *lhs_symbol_id) {
                            // If they're different, we report an error
                            if rhs_value != trace_value {
                                Err(ExecutionError::value_disagrees_with_trace(
                                    *rhs_expr_id,
                                    rhs_value,
                                    trace_value,
                                    *lhs_symbol_id, // Use LHS symbol for error reporting
                                    lhs_name.to_string(),
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

                                // If LHS is a DUT input port (has a parent) and RHS is a constant,
                                // add this as a constraint that must hold after stepping
                                if let Expr::Const(_) = rhs_expr {
                                    if self.symbol_table[*lhs_symbol_id].parent().is_some() {
                                        info!(
                                            "Adding constraint: {} must equal {}",
                                            lhs_name,
                                            serialize_bitvec(&rhs_value, ctx.display_hex)
                                        );
                                        self.constraints.insert(*lhs_symbol_id, rhs_value.clone());
                                    }
                                }

                                Ok(())
                            }
                        } else {
                            info!(
                                "Unable to find value for `{}` in trace at cycle {:?}",
                                lhs_name, self.trace_cycle_count
                            );
                            Err(ExecutionError::symbol_not_found(
                                *lhs_symbol_id,
                                lhs_name.to_string(),
                                "trace".to_string(),
                                *rhs_expr_id,
                            ))
                        }
                    }
                    Expr::Slice(sliced_expr_id, msb, lsb) => {
                        // In this case, we are taking a bitslice
                        // of an identifier that we've previously seen before
                        // (i.e. the identifier exists as a key
                        // in the `args_mapping`)

                        let sliced_expr = &self.transaction[sliced_expr_id];
                        match sliced_expr {
                            Expr::Sym(sliced_symbol_id) => {
                                let symbol_name = &self.symbol_table[sliced_symbol_id].name();
                                info!(
                                    "`{}`[{}:{}] evaluates to Concrete Value `{}`",
                                    symbol_name,
                                    msb,
                                    lsb,
                                    serialize_bitvec(&rhs_value, ctx.display_hex)
                                );

                                // Compare `rhs_value` (the value that
                                // `slice_expr[msb:lsb]` evaluates to)
                                // with the actual trace value
                                // (Note that we don't need to perform any
                                // further bit-slicing here, since we've
                                // already evaluated `slice_expr[msb:lsb]`

                                if let Ok(trace_value) = trace.get(ctx.instance_id, *lhs_symbol_id)
                                {
                                    // If they're different, we report an error
                                    if rhs_value != trace_value {
                                        Err(ExecutionError::value_disagrees_with_trace(
                                            *rhs_expr_id,
                                            rhs_value,
                                            trace_value,
                                            *lhs_symbol_id, // Use LHS symbol for error reporting
                                            lhs_name.to_string(),
                                            self.trace_cycle_count,
                                        ))
                                    } else {
                                        // The value matches the trace data,
                                        // so all we have to do is update
                                        // `known_bits` for `sliced_symbol_id`
                                        // by setting bits `[msb:lsb]` to 1
                                        let known_mask = self
                                            .known_bits
                                            .get_mut(sliced_symbol_id)
                                            .unwrap_or_else(|| {
                                                panic!(
                                                    "Missing entry in `known_bits` for {}",
                                                    symbol_name
                                                )
                                            });
                                        for idx in *lsb..=*msb {
                                            known_mask.set_bit(idx);
                                        }
                                        Ok(())
                                    }
                                } else {
                                    info!(
                                        "Unable to find value for `{}` in trace at cycle {:?}",
                                        lhs_name, self.trace_cycle_count
                                    );
                                    Err(ExecutionError::symbol_not_found(
                                        *lhs_symbol_id,
                                        lhs_name.to_string(),
                                        "trace".to_string(),
                                        *rhs_expr_id,
                                    ))
                                }
                            }
                            _ => {
                                // Illegal bit-slice operation
                                // (this will already have been caught by the type-checker)
                                Err(ExecutionError::illegal_slice(*rhs_expr_id, *msb, *lsb))
                            }
                        }
                    }
                    _ => todo!(
                        "Unhandled expr pattern {} which evaluates to {}",
                        serialize_expr(&self.transaction, &self.symbol_table, rhs_expr_id),
                        serialize_bitvec(&rhs_value, ctx.display_hex)
                    ),
                }
            }
            Ok(ExprValue::DontCare) => {
                // If the LHS is a DUT (input) port (e.g. `DUT.a`) and we
                // encountered a DontCare assignment `DUT.a := X`,
                // remove any constraints for it and any parameter bindings
                if self.symbol_table[*lhs_symbol_id].parent().is_some() {
                    self.constraints.remove(lhs_symbol_id);

                    // Also remove any parameter bindings that map to this port
                    // (e.g., if we had `data -> D.m_axis_tdata`, remove it)
                    self.args_to_pins
                        .retain(|_param_id, port_id| *port_id != *lhs_symbol_id);

                    info!(
                        "Cleared bindings for {} in `constraints` and `args_to_pins` due to DontCare assignment",
                        self.symbol_table[*lhs_symbol_id].full_name(&self.symbol_table)
                    );
                }
                Ok(())
            }
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
                        if let Ok(trace_value) = trace.get(ctx.instance_id, *lhs_symbol_id) {
                            self.args_mapping
                                .insert(*rhs_symbol_id, trace_value.clone());
                            info!(
                                "Updated args_mapping to map {} |-> {}",
                                symbol_name,
                                serialize_bitvec(&trace_value, ctx.display_hex)
                            );

                            // All the bits are known, so we insert a bit-string of
                            // all 1s into the `known_bits` map
                            // From type-checking, we know that the bitwidth of the
                            // LHS & RHS must be the same (otherwise the type-checker
                            // would have rejected the program)
                            let width = trace_value.width();
                            self.known_bits
                                .insert(*rhs_symbol_id, BitVecValue::ones(width));
                            info!("Updated known_bits to map {} |-> 111...1", symbol_name);

                            // Insert a mapping `rhs_symbol_id` |-> `lhs_symbol_id`
                            // into the `args_to_pins` map
                            // (the RHS is the function parameter,
                            // the LHS is a DUT pin)
                            self.args_to_pins.insert(*rhs_symbol_id, *lhs_symbol_id);
                            info!(
                                "Updated args_to_pins to map {} |-> {}",
                                symbol_name, lhs_name
                            );

                            // If there is an existing cosntraint for the DUT port (e.g. `DUT.a`)
                            // this means it was previously assigned some constant (e.g. `DUT.a := 5`),
                            // but now we are overwriting it with an assignment to an input parameter
                            // (e.g. `DUT.a := <input_param>`), so we should remove the constraint
                            if self.constraints.contains_key(lhs_symbol_id) {
                                self.constraints.remove(lhs_symbol_id);
                            }

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
                    // The case below corresponds to a bit-slice
                    // where the identifier being sliced hasn't been
                    // encountered before (i.e. is not in the args_mapping)
                    Expr::Slice(sliced_expr_id, msb, lsb) => {
                        let sliced_expr = &self.transaction[sliced_expr_id];
                        match sliced_expr {
                            Expr::Sym(sliced_symbol_id) => {
                                let symbol_name = self.symbol_table[sliced_symbol_id]
                                    .full_name(&self.symbol_table);
                                info!(
                                    "RHS of assignment is a bit-slice on an identifier `{}[{}:{}]` where `{}` is not in the args_mapping (adding it now...)",
                                    symbol_name, msb, lsb, symbol_name
                                );

                                // Look up the trace value corresponding
                                // to the LHS
                                if let Ok(trace_value) = trace.get(ctx.instance_id, *lhs_symbol_id)
                                {
                                    // Look up the width of `sliced_symbol_id`
                                    // based on its type in the `SymbolTable`.
                                    // Call this the `expected_width`
                                    // (the width is dictated by the type)
                                    let expected_width =
                                        self.symbol_table[sliced_symbol_id].tpe().bitwidth();
                                    info!("{} has type u{}", symbol_name, expected_width);

                                    // If `sliced_symbol_id` isn't currently
                                    // in either of `args_mapping` & `known_bits`,
                                    // map it to the bit-vector of all zeroes
                                    self.args_mapping
                                        .entry(*sliced_symbol_id)
                                        .or_insert_with(|| BitVecValue::zero(expected_width));
                                    self.known_bits
                                        .entry(*sliced_symbol_id)
                                        .or_insert_with(|| BitVecValue::zero(expected_width));

                                    // We have to clone these values in order
                                    // to satisfy the borrower checker
                                    let mut current_value =
                                        self.args_mapping[sliced_symbol_id].clone();
                                    let mut current_known_bits =
                                        self.known_bits[sliced_symbol_id].clone();

                                    // Update bits `[msb:lsb]` w/ the trace value
                                    for i in 0..=(msb - lsb) {
                                        let bit_pos = lsb + i;
                                        if trace_value.is_bit_set(i) {
                                            current_value.set_bit(bit_pos);
                                        } else {
                                            current_value.clear_bit(bit_pos);
                                        }
                                        // Mark this bit as known
                                        current_known_bits.set_bit(bit_pos);
                                    }

                                    // Update `args_mapping` and `known_bits`
                                    self.args_mapping
                                        .insert(*sliced_symbol_id, current_value.clone());
                                    self.known_bits
                                        .insert(*sliced_symbol_id, current_known_bits.clone());

                                    info!(
                                        "Updated args_mapping to map {} |-> {} (0b{})",
                                        symbol_name,
                                        serialize_bitvec(&current_value, ctx.display_hex),
                                        current_value.to_bit_str()
                                    );

                                    info!(
                                        "Updated known_bits to map {} |-> {}",
                                        symbol_name,
                                        current_known_bits.to_bit_str()
                                    );

                                    // Insert a mapping `sliced_symbol_id` |-> `lhs_symbol_id`
                                    // into the `args_to_pins` map
                                    // (the RHS is the function parameter,
                                    // the LHS is a DUT pin)
                                    self.args_to_pins.insert(*sliced_symbol_id, *lhs_symbol_id);
                                    info!(
                                        "Updated args_to_pins to map {} |-> {}",
                                        symbol_name, lhs_name
                                    );

                                    Ok(())
                                } else {
                                    Err(ExecutionError::symbol_not_found(
                                        *lhs_symbol_id,
                                        symbol_name,
                                        "trace".to_string(),
                                        *sliced_expr_id,
                                    ))
                                }
                            }
                            _ => {
                                // Illegal bit-slice operation
                                // (this will already have been caught by the type-checker)
                                Err(ExecutionError::illegal_slice(*sliced_expr_id, *msb, *lsb))
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
            Err(ExecutionError::Evaluation(EvaluationError::InvalidSlice {
                expr_id,
                start,
                end,
                width,
            })) => {
                panic!(
                    "Evaluation Error: Invalid slice {}[{}:{}] (actual width is {})",
                    serialize_expr(&self.transaction, &self.symbol_table, &expr_id),
                    start,
                    end,
                    width
                )
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
        trace: &WaveSignalTrace,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(loop_guard_id, ctx, trace)?;
        match res {
            ExprValue::DontCare => Err(ExecutionError::invalid_condition(
                "while".to_string(),
                *loop_guard_id,
            )),
            ExprValue::Concrete(bvv) => {
                if bvv.is_true() {
                    // Proceed to the next iteration of the loop
                    Ok(Some(*do_block_id))
                } else {
                    let next_stmt_str = match self.next_stmt_map[while_id] {
                        Some(next_stmt_id) => {
                            format!(
                                "{} ({})",
                                serialize_stmt(
                                    &self.transaction,
                                    &self.symbol_table,
                                    &next_stmt_id
                                ),
                                next_stmt_id
                            )
                        }
                        None => "No next stmt".to_string(),
                    };
                    info!(
                        "Loop guard `{}` evaluated to false, exiting loop, next stmt: `{}`",
                        serialize_expr(&self.transaction, &self.symbol_table, loop_guard_id),
                        next_stmt_str,
                    );
                    // Exit the loop, executing the statement that follows it immediately
                    Ok(self.next_stmt_map[while_id])
                }
            }
        }
    }

    /// Prints the reconstructed transaction
    /// (i.e. the function call that led to the signal trace)
    pub fn serialize_reconstructed_transaction(
        &self,
        ctx: &GlobalContext,
        trace: &WaveSignalTrace,
    ) -> String {
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
                let time_str = if ctx.show_waveform_time {
                    trace.format_time(trace.time_step(), ctx.time_unit)
                } else {
                    format!("cycle {}", self.trace_cycle_count) 
                };
                panic!(
                    "Transaction `{}`, {}: Unable to find value for {} ({}) in args_mapping, which is {{ {} }}",
                    self.transaction.name,
                    time_str,
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
