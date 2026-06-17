// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::Value;
use crate::dut::{PatronusSim, PortId};
use crate::errors::{ExecutionError, ExecutionResult};
use crate::frontend::ast::*;
use crate::frontend::serialize::serialize_bitvec;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::scheduler::Thread;
use baa::{BitVecOps, BitVecValue, WidthInt};
use log::info;
use rand::SeedableRng;
use rand::rngs::StdRng;
use rustc_hash::FxHashMap;

/// Per-thread input value: either a concrete assignment or DontCare
#[derive(Debug, Clone)]
pub enum ThreadInputValue {
    Concrete(BitVecValue),
    DontCare,
}

impl std::fmt::Display for ThreadInputValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ThreadInputValue::Concrete(bv) => write!(f, "{}", serialize_bitvec(bv, false)),
            ThreadInputValue::DontCare => write!(f, "DontCare"),
        }
    }
}

impl ThreadInputValue {
    pub fn is_concrete(&self) -> bool {
        matches!(self, ThreadInputValue::Concrete(_))
    }

    pub fn is_dont_care(&self) -> bool {
        matches!(self, ThreadInputValue::DontCare)
    }
}

/// Map from thread index (todo_idx) to input value for a single input pin.
///
/// The tuple contains:
/// - `ThreadInputValue`: The value assigned by this thread (Concrete or DontCare)
/// - `Option<StmtId>`: The statement that made this assignment, if any. This is `Some(stmt_id)`
///   for explicit assignments in the protocol code, and `None` for implicit DontCare
///   initialization at the start of a thread's first cycle. The StmtId is used for error
///   reporting to show the source location of conflicting assignments.
///
/// TODO: should this data be stored in the scheduler instead?
pub type PerThreadValues = FxHashMap<usize, (ThreadInputValue, Option<StmtId>)>;

/// An `ExprValue` is either a `Concrete` bit-vector value, or `DontCare`
#[derive(PartialEq, Debug, Clone)]
pub enum ExprValue {
    Concrete(BitVecValue),
    DontCare,
}

/// Type aliases for `Todo` indices (where a `Todo` is a protocol with
/// concrete argument values, e.g. `add(1, 2, 3)`)
pub type TodoIdx = usize;

/// An `Evaluator` evaluates ("interprets") a Protocols program.        
/// **Note**: The scope of the `Evaluator` is limited to executing a single
/// thread, with the `Scheduler` struct responsible for keeping track of
/// different threads.
pub struct Evaluator<'a> {
    tr: &'a Protocol,
    next_stmt_map: FxHashMap<StmtId, Option<StmtId>>,
    st: &'a SymbolTable,

    args_mapping: FxHashMap<SymbolId, Value>,

    /// _Dynamic:_ stack of loop variables, need to be searched right to left
    pub loop_vars: Vec<(SymbolId, BitVecValue)>,
    /// _Dynamic_: for-in/repeat loop information: loop statement id, max
    pub loop_info: Vec<(StmtId, u64, u64)>,

    /// Tracks inputs that are forbidden to assign to (after observing a dependent output)
    forbidden_inputs: Vec<PortId>,

    /// The `forbidden_read_counts` map maintains a count for each input and output pin.
    /// A port is forbidden to READ if its count is greater than zero.
    /// For inputs: count is incremented when DontCare is assigned, decremented when Concrete is assigned.
    /// For outputs: count is incremented when a dependent input is assigned DontCare, decremented when Concrete.
    /// This reference counting handles the case where multiple inputs affect the same output.
    forbidden_read_counts: FxHashMap<PortId, usize>,

    // Per-thread input values for each input pin: input_id -> (thread_id -> value)
    // This serves as both the current cycle's assignments AND the sticky inputs for implicit re-application
    per_thread_input_vals: FxHashMap<PortId, PerThreadValues>,

    /// The current todo_idx being executed
    /// (where a `todo` is a transaction with concrete argument values)
    current_todo_idx: TodoIdx,

    /// Whether `assert_eq` statements should be evaluated
    assertions_enabled: bool,

    /// Random number generator used for generating random values for `DontCare`
    rng: StdRng,
}

impl<'a> Evaluator<'a> {
    /// Pretty-prints a `Statement` identified by its `StmtId`
    /// with respect to the current `SymbolTable` associated with this `Evaluator`
    pub fn format_stmt(&self, stmt_id: StmtId) -> String {
        self.tr.format_stmt(&stmt_id, self.st)
    }

    /// Creates a new `Evaluator`
    pub fn new(
        args: FxHashMap<&str, Value>,
        tr: &'a Protocol,
        st: &'a SymbolTable,
        sim: &PatronusSim,
    ) -> Self {
        // create mapping from each symbolId to corresponding BitVecValue based on input mapping
        let args_mapping = Evaluator::generate_args_mapping(st, tr, args);

        // For simplicity, we initialize an RNG with the seed 0 when generating
        // random values for `DontCare`s
        let rng = StdRng::seed_from_u64(0);

        // Initialize per-thread input values (empty maps, populated when threads start)
        let per_thread_input_vals =
            FxHashMap::from_iter(sim.inputs().map(|i| (i, FxHashMap::default())));

        // Initialize forbidden read counts to 0 for all inputs and outputs
        let forbidden_read_counts = FxHashMap::from_iter(sim.ios().map(|p| (p, 0)));

        Evaluator {
            tr,
            next_stmt_map: tr.next_stmt_mapping(),
            st,
            args_mapping,
            forbidden_inputs: Vec::new(),
            forbidden_read_counts,
            per_thread_input_vals,
            current_todo_idx: 0,
            assertions_enabled: false,
            rng,
            loop_vars: vec![],
            loop_info: vec![],
        }
    }

    /// Creates a mapping from each symbolId to corresponding BitVecValue based on input mapping
    fn generate_args_mapping(
        st: &SymbolTable,
        proto: &Protocol,
        args: FxHashMap<&str, Value>,
    ) -> FxHashMap<SymbolId, Value> {
        let mut args_mapping = FxHashMap::default();
        for (name, value) in &args {
            if let Some(symbol_id) = st.symbol_id_from_name(proto.scope, name) {
                args_mapping.insert(symbol_id, (*value).clone());
            } else {
                panic!("Argument {} not found in DUT symbols.", name);
            }
        }
        args_mapping
    }

    /// Performs a context switch in the `Evaluator` by setting the `Evaluator`'s
    /// `Transaction` and `SymbolTable` to that of the specified `todo`
    pub fn context_switch(&mut self, thread: Thread<'a>) {
        self.tr = thread.todo.tr;
        self.st = thread.todo.st;
        self.args_mapping =
            Evaluator::generate_args_mapping(self.st, self.tr, thread.todo.args.clone());
        self.next_stmt_map = thread.todo.next_stmt_map.clone();
        self.current_todo_idx = thread.todo_idx;
        self.loop_info = thread.loop_info.clone();
        self.loop_vars = thread.loop_vars.clone();

        // Clear forbidden inputs (combinational dependency tracking)
        self.forbidden_inputs.clear();

        // Reset forbidden read counts to 0
        for count in self.forbidden_read_counts.values_mut() {
            *count = 0;
        }
    }

    /// Helper: applies an input value for a given thread.
    /// - Updates per_thread_input_vals
    /// - Updates forbidden_read_counts (for both this input and dependent outputs)
    /// - Applies value to sim immediately
    /// - For explicit assignments, `stmt_id` is Some(stmt_id). For implicit DontCare initialization, it's None.
    /// - Note: Conflict checking is deferred to `check_for_conflicts` at end of cycle.
    fn apply_input_value(
        &mut self,
        sim: &mut PatronusSim,
        port_id: PortId,
        todo_idx: usize,
        new_val: ThreadInputValue,
        stmt_id: Option<StmtId>,
    ) -> ExecutionResult<()> {
        // Get old value for this todo_idx (if any)
        let old_val = self
            .per_thread_input_vals
            .get(&port_id)
            .and_then(|m| m.get(&todo_idx))
            .map(|(val, _)| val.clone());

        // Handle forbidden_output reference counting
        let was_dontcare = matches!(old_val, Some(ThreadInputValue::DontCare));
        let is_dontcare = matches!(new_val, ThreadInputValue::DontCare);

        // Update forbidden_read_counts when transitioning to/from DontCare
        if is_dontcare && !was_dontcare {
            // Transitioning TO DontCare (from None or Concrete): increment counts
            // Increment this input's own forbidden count (can't read a DontCare input)
            if let Some(count) = self.forbidden_read_counts.get_mut(&port_id) {
                *count += 1;
            }
            // Increment forbidden counts for all outputs dependent on this input
            for dep in sim.dependent_outputs(port_id) {
                if let Some(count) = self.forbidden_read_counts.get_mut(&dep) {
                    *count += 1;
                }
            }
        } else if !is_dontcare && was_dontcare {
            // Transitioning FROM DontCare (to Concrete): decrement counts
            // Decrement this input's own forbidden count
            if let Some(count) = self.forbidden_read_counts.get_mut(&port_id) {
                *count = count.saturating_sub(1);
            }
            // Decrement forbidden counts for all outputs dependent on this input
            for dep in sim.dependent_outputs(port_id) {
                if let Some(count) = self.forbidden_read_counts.get_mut(&dep) {
                    *count = count.saturating_sub(1);
                }
            }
        }

        // Update per_thread_input_vals
        if let Some(per_thread_vals) = self.per_thread_input_vals.get_mut(&port_id) {
            let was_present = per_thread_vals.contains_key(&todo_idx);
            per_thread_vals.insert(todo_idx, (new_val.clone(), stmt_id));
            log::info!(
                "apply_input_value: {} for todo_idx={} (was_present={}, new_val={})",
                sim.port_name(port_id),
                todo_idx,
                was_present,
                new_val
            );
        }

        // Apply value to sim
        let any_other_concrete =
            if let Some(per_thread_vals) = self.per_thread_input_vals.get(&port_id) {
                per_thread_vals.iter().any(|(&other_idx, (other_val, _))| {
                    other_idx != todo_idx && matches!(other_val, ThreadInputValue::Concrete(_))
                })
            } else {
                false
            };

        log::info!(
            "Applying value for {} (todo_idx={}): any_other_concrete={}",
            sim.port_name(port_id),
            todo_idx,
            any_other_concrete
        );

        self.write_input_value_to_sim(sim, port_id, &new_val, !any_other_concrete);

        Ok(())
    }

    /// Initializes input values for a todo from its sticky inputs (implicit re-application)
    /// On first run, initializes all inputs to DontCare. On subsequent runs, reapplies existing values.
    pub fn init_thread_inputs(
        &mut self,
        sim: &mut PatronusSim,
        todo_idx: usize,
    ) -> ExecutionResult<()> {
        // Check if this is the first run for this thread (no entries in map)
        let is_first_run = self
            .per_thread_input_vals
            .values()
            .all(|per_thread_vals| !per_thread_vals.contains_key(&todo_idx));

        log::info!(
            "init_thread_inputs(todo_idx={}): is_first_run={}",
            todo_idx,
            is_first_run
        );

        if is_first_run {
            // First run: initialize all inputs to DontCare
            log::info!("  Initializing all inputs to DontCare");
            for port_id in sim.inputs() {
                log::info!(
                    "    Setting {} to DontCare (first run)",
                    sim.port_name(port_id)
                );
                self.apply_input_value(
                    sim,
                    port_id,
                    todo_idx,
                    ThreadInputValue::DontCare,
                    None, // DontCare initialization has no associated statement
                )?;
            }
        } else {
            // Subsequent runs: reapply existing values (implicit assignments)
            let inputs_to_init: Vec<_> = self
                .per_thread_input_vals
                .iter()
                .filter_map(|(symbol_id, per_thread_vals)| {
                    per_thread_vals
                        .get(&todo_idx)
                        .map(|(val, stmt_id)| (*symbol_id, val.clone(), *stmt_id))
                })
                .collect();

            for (port_id, val, stmt_id) in inputs_to_init {
                self.apply_input_value(sim, port_id, todo_idx, val, stmt_id)?;
            }
        }

        Ok(())
    }

    /// Clears a thread's input values (used when a thread completes and a new one starts fresh)
    pub fn clear_thread_inputs(&mut self, todo_idx: usize) {
        log::info!("Clearing thread inputs for todo_idx={}", todo_idx);
        for per_thread_vals in self.per_thread_input_vals.values_mut() {
            per_thread_vals.remove(&todo_idx);
        }
    }

    /// Returns a reference to the per-thread input values map for conflict checking.
    /// Used by the scheduler to check for conflicting assignments across threads.
    pub fn per_thread_input_vals(&self) -> &FxHashMap<PortId, PerThreadValues> {
        &self.per_thread_input_vals
    }

    /// Get the next statement after the given statement
    pub fn next_stmt(&self, stmt_id: &StmtId) -> Option<StmtId> {
        self.next_stmt_map.get(stmt_id).copied().flatten()
    }

    /// Called at end of cycle to finalize input values after conflict checking.
    /// For each input pin:
    /// - If any thread has a concrete value, apply it to sim (all concrete values must agree if no conflict)
    /// - If all threads have DontCare, randomize the pin
    pub fn finalize_inputs_for_cycle(&mut self, sim: &mut PatronusSim) {
        // Collect the values to apply (can't mutate self.per_thread_input_vals while iterating)
        let mut values_to_apply = vec![];

        for (port_id, per_thread_vals) in &self.per_thread_input_vals {
            // Find any concrete value (if conflicts were checked, all concrete values must agree)
            let concrete_val = per_thread_vals.values().find_map(|(val, _)| {
                if let ThreadInputValue::Concrete(bvv) = val {
                    Some(bvv.clone())
                } else {
                    None
                }
            });

            values_to_apply.push((*port_id, concrete_val));
        }

        // Now apply the values
        for (port_id, concrete_val) in values_to_apply {
            match concrete_val {
                Some(bvv) => {
                    // Apply the concrete value
                    sim.set(port_id, &bvv);
                }
                None => {
                    // All threads have DontCare, randomize
                    let width = sim.port_width(port_id);
                    let random_val = BitVecValue::random(&mut self.rng, width);
                    sim.set(port_id, &random_val);
                }
            }
        }
    }

    pub fn enable_assertions(&mut self) {
        self.assertions_enabled = true;
    }

    pub fn disable_assertions(&mut self) {
        self.assertions_enabled = false;
    }

    pub fn write_input_value_to_sim(
        &mut self,
        sim: &mut PatronusSim,
        port_id: PortId,
        value: &ThreadInputValue,
        randomize_dont_care: bool,
    ) {
        match value {
            ThreadInputValue::Concrete(bvv) => {
                sim.set(port_id, bvv);
            }
            ThreadInputValue::DontCare => {
                if randomize_dont_care {
                    let width = sim.port_width(port_id);
                    let random_val = BitVecValue::random(&mut self.rng, width);
                    sim.set(port_id, &random_val);
                }
            }
        }
    }

    pub fn evaluate_expr(
        &mut self,
        sim: &PatronusSim,
        expr_id: ExprId,
    ) -> ExecutionResult<ExprValue> {
        self.evaluate_expr_inner(sim, expr_id, true)
    }

    pub fn evaluate_expr_raw(
        &mut self,
        sim: &PatronusSim,
        expr_id: ExprId,
    ) -> ExecutionResult<ExprValue> {
        self.evaluate_expr_inner(sim, expr_id, false)
    }

    fn evaluate_expr_inner(
        &mut self,
        sim: &PatronusSim,
        expr_id: ExprId,
        check_forbidden_reads: bool,
    ) -> ExecutionResult<ExprValue> {
        let expr = self.tr[expr_id].clone();
        match expr {
            Expr::Const(bit_vec) => Ok(ExprValue::Concrete(bit_vec)),
            Expr::Sym(sym_id) => {
                let name = self.st[sym_id].full_name(self.st);

                // Check if reading this port is forbidden (count > 0)
                // For inputs: count > 0 when DontCare was assigned
                // For outputs: count > 0 when a dependent input has DontCare
                if self.st[sym_id].is_port() && check_forbidden_reads {
                    let port_id = sim[sym_id];
                    let count = self.forbidden_read_counts[&port_id];
                    if count > 0 {
                        // Collect the (full_name, stmt_id) of each DontCare input this port depends on
                        let unassigned_inputs: Vec<(String, Option<StmtId>)> = sim
                            .coi_inputs(port_id)
                            .filter_map(|input_port_id| {
                                let per_thread = self.per_thread_input_vals.get(&input_port_id)?;
                                // Find any thread that assigned DontCare to this input
                                let (_, (val, stmt_id)) =
                                    per_thread.iter().find(|(_, (val, _))| val.is_dont_care())?;
                                if val.is_dont_care() {
                                    Some((sim.port_name(input_port_id).to_string(), *stmt_id))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        return Err(ExecutionError::forbidden_port_read(
                            name.clone(),
                            unassigned_inputs,
                            expr_id,
                        ));
                    }
                }

                match self.st[sym_id].kind() {
                    SymbolKind::Dut => unreachable!("Cannot evaluate a struct expression!"),
                    SymbolKind::InPort => Ok(ExprValue::Concrete(sim.get(sim[sym_id]))),
                    SymbolKind::OutPort => {
                        let port_id = sim[sym_id];
                        // Observing an output port forbids assignments to its dependent inputs
                        self.forbidden_inputs.extend(sim.coi_inputs(port_id));
                        Ok(ExprValue::Concrete(sim.get(port_id)))
                    }
                    SymbolKind::Arg(_) => {
                        let value = self.args_mapping[&sym_id].clone();
                        Ok(ExprValue::Concrete(value.try_into().unwrap()))
                    }
                    SymbolKind::LoopVar => {
                        let (_, value) = self
                            .loop_vars
                            .iter()
                            .rev()
                            .find(|(id, _)| *id == sym_id)
                            .unwrap();
                        Ok(ExprValue::Concrete(value.clone()))
                    }
                }
            }
            Expr::DontCare => Ok(ExprValue::DontCare),
            Expr::IsLastIteration => {
                let (_, max_iter, iter_count) = self
                    .loop_info
                    .last()
                    .expect("is_last() must be inside of a loop!");
                let is_last = *iter_count + 1 == *max_iter;
                Ok(ExprValue::Concrete(BitVecValue::from_bool(is_last)))
            }
            Expr::IterCount(width) => {
                let (_, _, iter_count) = self
                    .loop_info
                    .last()
                    .expect("is_last() must be inside of a loop!");
                let mask = mask64(width);
                let value = BitVecValue::from_u64(*iter_count & mask, width);
                Ok(ExprValue::Concrete(value))
            }
            Expr::Binary(bin_op, lhs_id, rhs_id) => {
                let lhs_val = self.evaluate_expr_inner(sim, lhs_id, check_forbidden_reads)?;
                let rhs_val = self.evaluate_expr_inner(sim, rhs_id, check_forbidden_reads)?;
                match (&lhs_val, &rhs_val) {
                    (ExprValue::DontCare, _) | (_, ExprValue::DontCare) => {
                        Err(ExecutionError::dont_care_operation(
                            format!("{bin_op}"),
                            "binary expression".to_string(),
                            expr_id,
                        ))
                    }
                    (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => match bin_op {
                        BinOp::Equal => {
                            if lhs == rhs {
                                Ok(ExprValue::Concrete(BitVecValue::new_true()))
                            } else {
                                Ok(ExprValue::Concrete(BitVecValue::new_false()))
                            }
                        }
                        BinOp::Concat => Ok(ExprValue::Concrete(lhs.concat(rhs))),
                        BinOp::Add => Ok(ExprValue::Concrete(lhs.add(rhs))),
                        BinOp::And => Ok(ExprValue::Concrete(lhs.and(rhs))),
                    },
                }
            }
            Expr::Unary(unary_op, expr_id) => {
                let expr_val = self.evaluate_expr_inner(sim, expr_id, check_forbidden_reads)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => match unary_op {
                        UnaryOp::Not => Ok(ExprValue::Concrete(bvv.not())),
                    },
                    ExprValue::DontCare => Err(ExecutionError::dont_care_operation(
                        "unary operation".to_string(),
                        "unary expression".to_string(),
                        expr_id,
                    )),
                }
            }
            Expr::Slice(expr_id, msb, lsb) => {
                let expr_val = self.evaluate_expr_inner(sim, expr_id, check_forbidden_reads)?;
                match expr_val {
                    ExprValue::Concrete(bvv) => {
                        let width = bvv.width();
                        if msb < width && lsb <= msb {
                            Ok(ExprValue::Concrete(bvv.slice(msb, lsb)))
                        } else {
                            Err(ExecutionError::invalid_slice(expr_id, msb, lsb, width))
                        }
                    }
                    ExprValue::DontCare => Err(ExecutionError::dont_care_operation(
                        "slice".to_string(),
                        "slice expression".to_string(),
                        expr_id,
                    )),
                }
            }
        }
    }

    /// Evaluates the statement at the given `StmtId`. The additional argument
    /// `bounded_loop_remaining_iters` tracks the no. of loop iterations
    /// remaining for `repeat ...` loops. Callers of this function,
    /// e.g. in `scheduler.rs`, are meant to mutably borrow the
    /// `Thread.bounded_loop_remaining_iters` field and supply it as
    /// an argument to this function. This design allows us to keep this field
    /// only within the `Thread` struct and avoid duplicating it in the
    /// `Evaluator` struct.
    pub fn evaluate_stmt(
        &mut self,
        sim: &mut PatronusSim,
        stmt_id: StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        match self.tr[stmt_id].clone() {
            Stmt::Assign(symbol_id, expr_id) => {
                self.evaluate_assign(sim, stmt_id, symbol_id, expr_id)?;
                Ok(self.next_stmt_map[&stmt_id])
            }
            Stmt::IfElse(cond_expr_id, then_stmt_id, else_stmt_id) => {
                self.evaluate_if(sim, cond_expr_id, then_stmt_id, else_stmt_id)
            }
            Stmt::While(loop_guard_id, do_block_id) => {
                self.evaluate_while(sim, loop_guard_id, stmt_id, do_block_id)
            }
            Stmt::RepeatLoop(num_iters_id, loop_body_id) => {
                self.evaluate_bounded_loop(sim, num_iters_id, stmt_id, loop_body_id)
            }
            Stmt::ForInLoop(identifier, seq, loop_body_id) => {
                self.evaluate_for_in_loop(sim, identifier, seq, stmt_id, loop_body_id)
            }
            Stmt::Step => {
                // the scheduler will handle the step. simply return the next statement to run
                Ok(self.next_stmt_map[&stmt_id])
            }
            Stmt::Fork => {
                // the scheduler will handle the fork. simply return the next statement to run
                Ok(self.next_stmt_map[&stmt_id])
            }
            Stmt::AssertEq(expr1, expr2) => {
                if self.assertions_enabled {
                    self.evaluate_assert_eq(sim, stmt_id, expr1, expr2)?;
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
                    Ok(self.next_stmt_map[stmt_id])
                } else {
                    Ok(Some(stmt_ids[0]))
                }
            }
        }
    }

    fn evaluate_if(
        &mut self,
        sim: &PatronusSim,
        cond_expr_id: ExprId,
        then_stmt_id: StmtId,
        else_stmt_id: StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(sim, cond_expr_id)?;
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
    /// is the `StmtId` of the assignment statement.
    fn evaluate_assign(
        &mut self,
        sim: &mut PatronusSim,
        stmt_id: StmtId,
        symbol_id: SymbolId,
        expr_id: ExprId,
    ) -> ExecutionResult<()> {
        // Check if this is an input pin
        if !self.input_mapping.contains_key(symbol_id) {
            let name = self.st[symbol_id].full_name(self.st);
            if self.output_mapping.contains_key(symbol_id) {
                return Err(ExecutionError::read_only_assignment(
                    *symbol_id,
                    name.to_string(),
                    "outputs".to_string(),
                    *stmt_id,
                ));
            } else if self.args_mapping.contains_key(symbol_id) {
                return Err(ExecutionError::read_only_assignment(
                    *symbol_id,
                    name.to_string(),
                    "arguments".to_string(),
                    *stmt_id,
                ));
            } else {
                return Err(ExecutionError::symbol_not_found(
                    *symbol_id,
                    name.to_string(),
                    "symbol mappings".to_string(),
                    *expr_id,
                ));
            }
        }

        let expr_val = self.evaluate_expr(expr_id)?;
        let todo_idx = self.current_todo_idx;

        // Check if assigning to this input port is forbidden (after observing a dependent output)
        if self.forbidden_inputs.contains(symbol_id) {
            let name = self.st[symbol_id].name();
            return Err(ExecutionError::forbidden_input_assignment(
                name.to_string(),
                *expr_id,
            ));
        }

        // Determine new value
        let new_val = match expr_val {
            ExprValue::Concrete(bvv) => ThreadInputValue::Concrete(bvv),
            ExprValue::DontCare => ThreadInputValue::DontCare,
        };

        // Use helper to check conflicts, update state, and apply to sim
        self.apply_input_value(symbol_id, todo_idx, new_val, Some(*stmt_id))
    }

    fn evaluate_while(
        &mut self,
        sim: &PatronusSim,
        loop_guard_id: ExprId,
        while_id: StmtId,
        do_block_id: StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        let res = self.evaluate_expr(sim, loop_guard_id)?;
        match res {
            ExprValue::DontCare => Err(ExecutionError::invalid_condition(
                "while".to_string(),
                loop_guard_id,
            )),
            ExprValue::Concrete(bvv) => {
                if bvv.is_true() {
                    Ok(Some(do_block_id))
                } else {
                    Ok(self.next_stmt_map[&while_id])
                }
            }
        }
    }

    /// Evaluates a bounded loop (loop with a fixed no. of iterations).
    /// Arguments are the `ExprId`s/`StmtId`s for the no. of iterations,
    /// the entire loop statement and the loop body itself. The final arguemnt
    /// `bounded_loop_remaining_iters` tracks the no. of iterations remaining
    /// for `repeat ...` loops (it is meant to be used as a mutable borrow
    /// of the field `Thread.bounded_loops_remaining_iters` from the appropriate
    /// thread).
    fn evaluate_bounded_loop(
        &mut self,
        num_iters_id: &ExprId,
        bounded_loop_id: &StmtId,
        loop_body_id: &StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        // check to see if there is an entry for this loop
        if let Some((info_stmt_id, max_iter, iter_count)) = self.loop_info.last().cloned()
            && info_stmt_id == *bounded_loop_id
        {
            // we are already executing this loop
            self.loop_info.pop().unwrap();
            if iter_count + 1 == max_iter {
                // done
                Ok(self.next_stmt_map[bounded_loop_id])
            } else {
                self.loop_info
                    .push((*bounded_loop_id, max_iter, iter_count + 1));
                Ok(Some(*loop_body_id))
            }
        } else {
            // start loop execution
            // We've not encountered this bounded loop before,
            // so we have to evaluate the no. of iters that the user specified
            let num_iters_result = self.evaluate_expr(num_iters_id)?;
            match num_iters_result {
                ExprValue::DontCare => {
                    // No. of loop iterations can't be `DontCare`
                    Err(ExecutionError::invalid_condition(
                        "bounded_loop".to_string(),
                        *num_iters_id,
                    ))
                }
                ExprValue::Concrete(bvv) => {
                    let num_iterations = bvv
                        .to_u64()
                        .expect("Expected no. of loop iterations in a bounded loop to be an unsigned integer");

                    // If the user wrote `repeat 0 iterations { ... }`,
                    // skip the loop and proceed to the next stmt
                    if num_iterations == 0 {
                        Ok(self.next_stmt_map[bounded_loop_id])
                    } else {
                        // Keep track of the no. of loop iterations,
                        // and execute the loop body
                        self.loop_info.push((*bounded_loop_id, num_iterations, 0));
                        Ok(Some(*loop_body_id))
                    }
                }
            }
        }
    }

    fn evaluate_for_in_loop(
        &mut self,
        loop_var_sym: &SymbolId,
        seq: &ExprId,
        stmt_id: &StmtId,
        loop_body_id: &StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        // figure out size of seq
        let seq_symbol_id = if let Expr::Sym(id) = &self.tr[seq] {
            id
        } else {
            unreachable!("The sequence in an evaluate for loop must always be a symbol.");
        };
        let seq_values: &[BitVecValue] = (&self.args_mapping[seq_symbol_id]).try_into().unwrap();

        // check to see if there is an entry for this loop
        if let Some((info_stmt_id, max_iter, iter_count)) = self.loop_info.last().cloned()
            && info_stmt_id == *stmt_id
        {
            // we are already executing this loop
            self.loop_info.pop().unwrap();
            let (var_sym_id, _) = self.loop_vars.pop().unwrap();
            assert_eq!(var_sym_id, *loop_var_sym);
            if iter_count + 1 == max_iter {
                Ok(self.next_stmt_map[stmt_id])
            } else {
                self.loop_vars
                    .push((var_sym_id, seq_values[iter_count as usize + 1].clone()));
                self.loop_info.push((*stmt_id, max_iter, iter_count + 1));
                Ok(Some(*loop_body_id))
            }
        } else {
            // start loop execution
            if seq_values.is_empty() {
                Ok(self.next_stmt_map[stmt_id])
            } else {
                self.loop_vars.push((*loop_var_sym, seq_values[0].clone()));
                self.loop_info.push((*stmt_id, seq_values.len() as u64, 0));
                Ok(Some(*loop_body_id))
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

#[inline]
fn mask64(width: WidthInt) -> u64 {
    debug_assert!(width <= 64);
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}
