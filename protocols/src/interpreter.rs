// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::errors::{ExecutionError, ExecutionResult};
use crate::ir::*;
use crate::scheduler::Todo;
use crate::serialize::serialize_bitvec;
use baa::{BitVecOps, BitVecValue};
use log::info;
use patronus::expr::ExprRef;
use patronus::sim::{InitKind, Interpreter, Simulator};
use patronus::system::Output;
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
/// TODO: should we change this to a new-type instead, e.g. `struct TodoIdx(u32)`
/// and use the `entity_impl!` macro (similar to `StmtId`)?
/// This would require a map to keep track of `TodoIdx |-> todo` bindings though,
/// so may be more trouble than its worth.
type TodoIdx = usize;

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
    /// Maps `input |-> Vec<output>` (outputs that are affected by this input)
    input_dependencies: FxHashMap<SymbolId, Vec<SymbolId>>,

    /// Maps each `output |-> Vec<input>` (inputs that this output is dependent on)
    output_dependencies: FxHashMap<SymbolId, Vec<SymbolId>>,

    // tracks forbidden ports due to combinational dependencies
    forbidden_inputs: Vec<SymbolId>,

    /// The `forbidden_output_counts` map maintains a count for each output pin.
    /// When a thread assigns an input from `Concrete` to `DontCare`, we increment
    /// the count for all outputs combinationally dependent on that input.
    /// When a thread assigns from `DontCare` to `Concrete`, we decrement those counts.
    /// This reference counting is necessary because multiple input pins can
    /// affect the same output pin combinationally;
    /// after setting one input to `Concrete`, we cannot simply clear the
    /// forbidden status of the output;
    /// we must decrement its count by one. An output is forbidden to observe
    /// if its count is greater than zero, meaning at least one input in its
    /// combinational cone is currently assigned to DontCare.
    forbidden_output_counts: FxHashMap<SymbolId, usize>,

    // Per-thread input values for each input pin: input_id -> (thread_id -> value)
    // This serves as both the current cycle's assignments AND the sticky inputs for implicit re-application
    per_thread_input_vals: FxHashMap<SymbolId, PerThreadValues>,

    /// The current todo_idx being executed
    /// (where a `todo` is a transaction with concrete argument values)
    current_todo_idx: TodoIdx,

    /// Maps a `(TodoIdx, StmtId)` pair (representing a protocol that is
    /// executing a particular bounded loop) to the no. of iterations remaining
    /// for that particular loop.              
    /// - **Invariant**: the no. of remaining iterations is always non-zero
    ///   (if it reaches zero, we remove the entry from this map).       
    /// - In the key, we need the `StmtId` to allow for nested loops,
    ///   and we also need the `TodoIdx`, since the same `StmtId` could be active
    ///   in differnt threads.
    bounded_loop_remaining_iters: FxHashMap<(TodoIdx, StmtId), u64>,

    /// Whether `assert_eq` statements should be evaluated
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
        let rng = StdRng::seed_from_u64(0);

        // Initialize per-thread input values (empty maps, populated when threads start)
        let mut per_thread_input_vals = FxHashMap::default();
        for symbol_id in input_mapping.keys() {
            // Verify the symbol has a BitVec type
            match st[symbol_id].tpe() {
                Type::BitVec(_) => {
                    per_thread_input_vals.insert(*symbol_id, FxHashMap::default());
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

        // Initialize forbidden output counts to 0
        let mut forbidden_output_counts = FxHashMap::default();
        for symbol_id in output_mapping.keys() {
            forbidden_output_counts.insert(*symbol_id, 0);
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
            forbidden_output_counts,
            per_thread_input_vals,
            bounded_loop_remaining_iters: FxHashMap::default(),
            current_todo_idx: 0,
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
    /// Performs a context switch to execute a different thread
    pub fn context_switch(&mut self, todo: Todo<'a>, todo_idx: usize) {
        self.tr = todo.tr;
        self.st = todo.st;
        self.args_mapping = Evaluator::generate_args_mapping(self.st, todo.args);
        self.next_stmt_map = todo.next_stmt_map;
        self.current_todo_idx = todo_idx;

        // Clear forbidden ports when switching to a new thread context
        self.forbidden_inputs.clear();

        // Reset forbidden output counts to 0
        for count in self.forbidden_output_counts.values_mut() {
            *count = 0;
        }
    }

    /// Helper: applies an input value for a given thread.
    /// - Updates per_thread_input_vals
    /// - Updates forbidden_output_counts
    /// - Applies value to sim immediately
    /// - For explicit assignments, `stmt_id` is Some(stmt_id). For implicit DontCare initialization, it's None.
    /// - Note: Conflict checking is deferred to `check_for_conflicts` at end of cycle.
    fn apply_input_value(
        &mut self,
        symbol_id: &SymbolId,
        todo_idx: usize,
        new_val: ThreadInputValue,
        stmt_id: Option<StmtId>,
    ) -> ExecutionResult<()> {
        // Get old value for this todo_idx (if any)
        let old_val = self
            .per_thread_input_vals
            .get(symbol_id)
            .and_then(|m| m.get(&todo_idx))
            .map(|(val, _)| val.clone());

        // Handle forbidden_output reference counting
        let was_dontcare = matches!(old_val, Some(ThreadInputValue::DontCare));
        let is_dontcare = matches!(new_val, ThreadInputValue::DontCare);

        // Update counts when transitioning to/from DontCare
        if is_dontcare && !was_dontcare {
            // Transitioning TO DontCare (from None or Concrete): increment counts
            if let Some(deps) = self.input_dependencies.get(symbol_id) {
                for dep in deps {
                    if let Some(count) = self.forbidden_output_counts.get_mut(dep) {
                        *count += 1;
                    }
                }
            }
        } else if !is_dontcare && was_dontcare {
            // Transitioning FROM DontCare (to Concrete): decrement counts
            if let Some(deps) = self.input_dependencies.get(symbol_id) {
                for dep in deps {
                    if let Some(count) = self.forbidden_output_counts.get_mut(dep) {
                        *count = count.saturating_sub(1);
                    }
                }
            }
        }

        // Update per_thread_input_vals
        if let Some(per_thread_vals) = self.per_thread_input_vals.get_mut(symbol_id) {
            let symbol_name = self.st[*symbol_id].name();
            let was_present = per_thread_vals.contains_key(&todo_idx);
            per_thread_vals.insert(todo_idx, (new_val.clone(), stmt_id));
            log::info!(
                "apply_input_value: {} for todo_idx={} (was_present={}, new_val={})",
                symbol_name,
                todo_idx,
                was_present,
                new_val
            );
        }

        // Apply value to sim
        if let Some(expr_ref) = self.input_mapping.get(symbol_id) {
            match new_val {
                ThreadInputValue::Concrete(bvv) => {
                    // Always apply Concrete values immediately
                    self.sim.set(*expr_ref, &bvv);
                }
                ThreadInputValue::DontCare => {
                    // Check if any OTHER thread has Concrete for this pin
                    let any_other_concrete =
                        if let Some(per_thread_vals) = self.per_thread_input_vals.get(symbol_id) {
                            per_thread_vals.iter().any(|(&other_idx, (other_val, _))| {
                                other_idx != todo_idx
                                    && matches!(other_val, ThreadInputValue::Concrete(_))
                            })
                        } else {
                            false
                        };

                    let symbol_name = self.st[*symbol_id].name();
                    log::info!(
                        "Applying DontCare for {} (todo_idx={}): any_other_concrete={}",
                        symbol_name,
                        todo_idx,
                        any_other_concrete
                    );

                    // If all other threads have DontCare, randomize
                    if !any_other_concrete {
                        let width = match self.st[*symbol_id].tpe() {
                            Type::BitVec(w) => w,
                            _ => panic!("Expected BitVec type for input"),
                        };
                        let random_val = BitVecValue::random(&mut self.rng, width);
                        log::info!("  Randomizing {} to {:?}", symbol_name, random_val);
                        self.sim.set(*expr_ref, &random_val);
                    } else {
                        log::info!(
                            "  NOT randomizing {} (another thread has Concrete)",
                            symbol_name
                        );
                    }
                    // Otherwise do nothing - leave the Concrete value in place
                }
            }
        }

        Ok(())
    }

    /// Initializes input values for a todo from its sticky inputs (implicit re-application)
    /// On first run, initializes all inputs to DontCare. On subsequent runs, reapplies existing values.
    pub fn init_thread_inputs(&mut self, todo_idx: usize) -> ExecutionResult<()> {
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

        // Debug: show which inputs have this todo_idx
        for (symbol_id, per_thread_vals) in &self.per_thread_input_vals {
            if per_thread_vals.contains_key(&todo_idx) {
                let symbol_name = self.st[*symbol_id].name();
                log::info!(
                    "  {} already has entry for todo_idx={}",
                    symbol_name,
                    todo_idx
                );
            }
        }

        if is_first_run {
            // First run: initialize all inputs to DontCare
            let all_inputs: Vec<SymbolId> = self.input_mapping.keys().copied().collect();
            log::info!("  Initializing {} inputs to DontCare", all_inputs.len());
            for symbol_id in all_inputs {
                let symbol_name = self.st[symbol_id].name();
                log::info!("    Setting {} to DontCare (first run)", symbol_name);
                self.apply_input_value(
                    &symbol_id,
                    todo_idx,
                    ThreadInputValue::DontCare,
                    None, // DontCare initialization has no associated statement
                )?;
            }
        } else {
            // Subsequent runs: reapply existing values (implicit assignments)
            let inputs_to_init: Vec<(SymbolId, ThreadInputValue, Option<StmtId>)> = self
                .per_thread_input_vals
                .iter()
                .filter_map(|(symbol_id, per_thread_vals)| {
                    per_thread_vals
                        .get(&todo_idx)
                        .map(|(val, stmt_id)| (*symbol_id, val.clone(), *stmt_id))
                })
                .collect();

            for (symbol_id, val, stmt_id) in inputs_to_init {
                self.apply_input_value(&symbol_id, todo_idx, val, stmt_id)?;
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
    pub fn per_thread_input_vals(&self) -> &FxHashMap<SymbolId, PerThreadValues> {
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
    pub fn finalize_inputs_for_cycle(&mut self) {
        // Collect the values to apply (can't mutate self.per_thread_input_vals while iterating)
        let mut values_to_apply: Vec<(SymbolId, Option<BitVecValue>)> = Vec::new();

        for (symbol_id, per_thread_vals) in &self.per_thread_input_vals {
            // Find any concrete value (if conflicts were checked, all concrete values must agree)
            let concrete_val = per_thread_vals.values().find_map(|(val, _)| {
                if let ThreadInputValue::Concrete(bvv) = val {
                    Some(bvv.clone())
                } else {
                    None
                }
            });

            values_to_apply.push((*symbol_id, concrete_val));
        }

        // Now apply the values
        for (symbol_id, concrete_val) in values_to_apply {
            if let Some(expr_ref) = self.input_mapping.get(&symbol_id) {
                match concrete_val {
                    Some(bvv) => {
                        // Apply the concrete value
                        self.sim.set(*expr_ref, &bvv);
                    }
                    None => {
                        // All threads have DontCare, randomize
                        let width = match self.st[symbol_id].tpe() {
                            Type::BitVec(w) => w,
                            _ => panic!("Expected BitVec type for input"),
                        };
                        let random_val = BitVecValue::random(&mut self.rng, width);
                        self.sim.set(*expr_ref, &random_val);
                    }
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

    /// Steps the simulator
    pub fn sim_step(&mut self) {
        self.sim.step();
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
                    // Check if observing this output port is forbidden (count > 0)
                    // The count is > 0 when a DontCare value was assigned to a dependent input
                    if let Some(&count) = self.forbidden_output_counts.get(sym_id) {
                        if count > 0 {
                            return Err(ExecutionError::forbidden_output_observation(
                                name.to_string(),
                                *expr_id,
                            ));
                        }
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
            Stmt::BoundedLoop(num_iters_id, loop_body_id) => {
                self.evaluate_bounded_loop(num_iters_id, stmt_id, loop_body_id)
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
                    Ok(self.next_stmt_map[stmt_id])
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
    /// is the `StmtId` of the assignment statement.
    fn evaluate_assign(
        &mut self,
        stmt_id: &StmtId,
        symbol_id: &SymbolId,
        expr_id: &ExprId,
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

        // Check if assigning to this input port is forbidden (after evaluating RHS)
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

    /// Evaluates a bounded loop (loop with a fixed no. of iterations).
    /// Arguments are the `ExprId`s/`StmtId`s for the no. of iterations,
    /// the entire loop statement and the loop body itself.
    fn evaluate_bounded_loop(
        &mut self,
        num_iters_id: &ExprId,
        bounded_loop_id: &StmtId,
        loop_body_id: &StmtId,
    ) -> ExecutionResult<Option<StmtId>> {
        // Key for the `bounded_loop_remaining_iters` map, which tracks
        // the no. of iterations remaining for each bounded loop
        let key = (self.current_todo_idx, *bounded_loop_id);
        if let Some(num_iterations) = self.bounded_loop_remaining_iters.get_mut(&key) {
            *num_iterations -= 1;
            if *num_iterations == 0 {
                // Exit the loop
                self.bounded_loop_remaining_iters.remove(&key);
                Ok(self.next_stmt_map[bounded_loop_id])
            } else {
                // There are still non-zero iterations remaining,
                // so execute the loop body again
                Ok(Some(*loop_body_id))
            }
        } else {
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
                        .expect("Expected no. of loop iterations in a bounded loop to be a u64");

                    // If the user wrote `repeat 0 iterations { ... }`,
                    // skip the loop and proceed to the next stmt
                    if num_iterations == 0 {
                        Ok(self.next_stmt_map[bounded_loop_id])
                    } else {
                        // Keep track of the no. of loop iterations,
                        // and execute the loop body
                        self.bounded_loop_remaining_iters
                            .insert(key, num_iterations);
                        Ok(Some(*loop_body_id))
                    }
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
