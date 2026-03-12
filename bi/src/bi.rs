// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::signal_trace::{SignalTrace, StepResult};
use baa::{BitVecOps, BitVecValue};
use protocols::ir::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub type ProtoTrace = Vec<(String, Vec<Option<BitVecValue>>)>;

pub struct BackwardsInterpreter<T: SignalTrace> {
    trace: T,
    transactions: Vec<TransactionInfo>,
    instance_id: u32,
    step: u32,
    active: Vec<Path>,
    finished: Vec<Path>,
    failed: Vec<Path>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BIResult {
    Ok,
    Done,
    Fail,
}

impl<T: SignalTrace> BackwardsInterpreter<T> {
    pub fn new(
        transactions_and_symbols: Vec<(Transaction, SymbolTable)>,
        trace: T,
        instance_id: u32,
    ) -> Self {
        let transactions: Vec<_> = transactions_and_symbols
            .into_iter()
            .map(|(t, _)| t.into())
            .collect();
        let step = 0;
        let active = Path::default().fork(transactions.iter(), false);

        Self {
            transactions,
            trace,
            instance_id,
            step,
            active,
            finished: vec![],
        }
    }

    pub fn run(&mut self) -> BIResult {

    }


    /// execute a single step
    fn exec(&mut self) {
        if let Some(mut path) = self.active.pop() {
            // execute one path
            let r = path.exec(&self.transactions, &|sym| self.trace.get(self.instance_id, sym));
            match r {
                PathResult::Fork(delayed) => {
                    let mut new_paths = path.fork(self.transactions.iter(), delayed);
                    debug_assert!(new_paths.iter().all(|p| !p.step_finished()));
                    self.active.append(&mut new_paths);
                }
                PathResult::Ok => {
                    debug_assert!(!path.step_finished() && !path.failed());
                    self.active.push(path);
                }
                PathResult::Failed => {
                    debug_assert!(path.failed());
                    self.failed.push(path);
                }
                PathResult::FinishedStep => {
                    debug_assert!(path.step_finished() && !path.failed());
                    self.finished.push(path);
                }
            }
        } else {
            // otherwise all paths must be finished
            debug_assert!(self.active.is_empty());
            debug_assert!(self.finished.iter().all(|p| p.step == self.step && p.step_finished() && !p.failed()));
            debug_assert!(self.failed.iter().all(|p| p.failed()));
            let all_failed = self.finished.is_empty();
            if all_failed {
                todo!("show good error message when all paths fail")
            } else {
                // discard failed paths and prepare others for next step
                self.failed.clear();
                for mut path in self.finished.drain(..) {
                    path.active.append(&mut path.next);
                    self.active.push(path);
                }
                // step trace
                match self.trace.step() {
                    StepResult::Ok => {}
                    StepResult::Done => { todo!("trace done!") }
                }
            }
        }
    }
}

/// An execution path.
#[derive(Debug, Clone, Default)]
struct Path {
    /// identifier for the protocol trace associated with this execution path
    trace_id: usize,
    active: Vec<Thread>,
    failed: Vec<Thread>,
    next: Vec<Thread>,
    step: u32,
}

#[derive(Debug, Clone)]
enum PathResult {
    Fork(bool),
    Ok,
    Failed,
    FinishedStep,
}

impl Path {

    fn fork<'a>(
        self,
        transactions: impl Iterator<Item = &'a TransactionInfo>,
        delayed: bool,
    ) -> Vec<Self> {
        debug_assert!(self.failed.is_empty());
        transactions
            .enumerate()
            .map(move |(id, t)| {
                let mut p = self.clone();
                let t = Thread {
                    name: t.transaction.name.clone(),
                    transaction_id: id,
                    next_stmt: Some(t.transaction.body),
                    arg_values: vec![None; t.transaction.args.len()],
                    has_forked: false,
                    steps: 0,
                    pin_assignments: vec![],
                };
                if delayed {
                    p.next.push(t);
                } else {
                    p.active.push(t);
                }
                p
            })
            .collect()
    }

    fn step_finished(&self) -> bool {
        self.active.is_empty()
    }

    fn failed(&self) -> bool {
        !self.failed.is_empty()
    }

    fn exec(
        &mut self,
        tis: &[TransactionInfo],
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> PathResult {
        if let Some(mut t) = self.active.pop() {
            match t.exec(&tis[t.transaction_id], get_value) {
                ThreadResult::Ok => {}
                ThreadResult::Step => {}
                ThreadResult::Fork => {}
                ThreadResult::StepAndFork => {}
                ThreadResult::Finished => {
                    todo!("extend trace from the finished thread")
                }
                ThreadResult::Failed => PathResult::Failed,
            }
        } else {
            PathResult::FinishedStep
        }
    }
}

#[derive(Debug, Clone)]
struct Thread {
    name: String,
    transaction_id: usize,
    next_stmt: Option<StmtId>,
    arg_values: Vec<Option<BitVecValue>>,
    pin_assignments: Vec<(SymbolId, ExprId)>,
    has_forked: bool,
    steps: u32,
}

#[derive(Debug, Clone)]
enum ThreadResult {
    Ok,
    Step,
    Fork,
    FinalStepAndFork,
    FinalStep,
    Failed,
}

impl Thread {
    fn exec(
        &mut self,
        ti: &TransactionInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        use ThreadResult::*;
        if let Some(stmt) = self.next_stmt {
            let (next_stmt, result) = match &ti.transaction[stmt] {
                Stmt::Block(stmt_ids) => (stmt_ids.first().cloned(), Ok),
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    self.pin_assignments.push((*lhs, *rhs));
                    (ti.next_stmt[&stmt], Ok)
                }
                Stmt::Step => {
                    let next_stmt = ti.next_stmt[&stmt];
                    self.steps += 1;
                    let assign_ok = self.check_assignments(&ti.transaction, get_value);

                    let r = match (assign_ok, next_stmt.is_none(), self.has_forked) {
                        (true, _, _) => Failed,
                        (false, true, false) => FinalStepAndFork,
                        (false, true, true) => FinalStep,
                        (false, false, _) => Step,
                    }

                    if assign_ok {
                        if next_stmt.is_none() {
                            if !self.has_forked {
                                (None, StepAndFork)
                            } else {
                                (None, Step)
                            }
                        }
                    }

                    let r = if thread.next_stmt.is_none() {
                        crate::bi2::ExecThreadResult::Finished
                    } else {
                        crate::bi2::ExecThreadResult::Yield
                    };
                    (ti.next_stmt[&stmt], Ok)
                }
                Stmt::Fork => {
                    thread.has_forked = true;
                    next_stmts[&stmt]
                }
                Stmt::While(cond, body) => {
                    let cond_value = self
                        .eval_expr(get_value, &transaction, thread, *cond)
                        .expect("while condition is always concrete");
                    if cond_value.is_true() {
                        Some(*body)
                    } else {
                        next_stmts[&stmt]
                    }
                }
                Stmt::RepeatLoop(repetitions, body) => {
                    let (arg_id, arg) = crate::bi2::as_arg(transaction, *repetitions)
                        .expect("repeat loop repetition count needs to be an argument");

                    todo!("repeat {:?}", arg.symbol())
                }
                Stmt::IfElse(cond, tru, fals) => {
                    let cond_value = self
                        .eval_expr(get_value, &transaction, thread, *cond)
                        .expect("if condition is always concrete");
                    if cond_value.is_true() {
                        Some(*tru)
                    } else {
                        Some(*fals)
                    }
                }
                Stmt::AssertEq(lhs, rhs) => {
                    let (port, other) = match (
                        crate::bi2::as_dut_port_symbol(&transaction, *lhs),
                        crate::bi2::as_dut_port_symbol(&transaction, *rhs),
                    ) {
                        (Some(port), _) => (port, *rhs),
                        (_, Some(port)) => (port, *lhs),
                        (None, None) => {
                            todo!("we currently expect one side of an assert_eq to be a port!")
                        }
                    };
                    if self.exec_equality(get_value, &transaction, thread, port, other) {
                        next_stmts[&stmt]
                    } else {
                        return (
                            crate::bi2::ExecThreadResult::Failed,
                            thread.has_forked && !forked_before,
                        );
                    }
                }
            };
            self.next_stmt = next_stmt;
            result
        } else {
            ThreadResult::Finished
        }
    }

    /// Must be called at the end of a step in order to check all equality constraints
    /// imposed by assignments in the current step.
    fn check_assignments(
        &mut self,
        transaction: &Transaction,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> bool {
        let mut pins_assigned = FxHashSet::default();
        let assignments = std::mem::take(&mut self.pin_assignments);
        // go from last assignment to first
        for (pin, expr) in assignments.into_iter().rev() {
            // only the final assignment to a pin matters
            if !pins_assigned.contains(&pin) {
                pins_assigned.insert(pin);
                if !self.exec_equality(get_value, transaction, pin, expr) {
                    // early exit on failure
                    return false;
                } else if !matches!(transaction[expr], Expr::DontCare) {
                    // assignment sticks around for the next step
                    self.pin_assignments.push((pin, expr));
                }
            }
        }
        true
    }

    /// used for both assert_eq and assignments
    fn exec_equality(
        &mut self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        transaction: &Transaction,
        lhs: SymbolId,
        rhs: ExprId,
    ) -> bool {
        // a DontCare imposes no constraints and thus there is nothing to learn, nothing to check
        if matches!(transaction[rhs], Expr::DontCare) {
            return true;
        }

        let lhs_value = get_value(lhs);
        if let Some(rhs_value) = self.eval_expr(get_value, transaction, rhs) {
            if rhs_value != lhs_value {
                // println!(
                //     "[{}] found a disagreement: {} =/= {}",
                //     transaction.name,
                //     lhs_value.to_bit_str(),
                //     rhs_value.to_bit_str()
                // );
            }
            rhs_value == lhs_value
        } else {
            if let Some((arg_id, _arg)) = as_arg(&transaction, rhs) {
                debug_assert!(self.arg_values[arg_id].is_none());
                // println!(
                //     "[{}] Discovered that {} = {}",
                //     transaction.name,
                //     transactions[thread.transaction_id].symbol_table[lhs].name(),
                //     lhs_value.to_bit_str()
                // );
                self.arg_values[arg_id] = Some(lhs_value);
            } else {
                todo!()
            }
            true
        }
    }

    fn eval_expr(
        &self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        transaction: &Transaction,
        expr: ExprId,
    ) -> Option<BitVecValue> {
        if let Some((arg_id, _)) = as_arg(transaction, expr) {
            return self.arg_values[arg_id].clone();
        }
        match &transaction[expr] {
            Expr::Const(value) => Some(value.clone()),
            Expr::Sym(dut_port) => Some(get_value(*dut_port)),
            Expr::DontCare => None,
            Expr::Binary(op, a, b) => {
                self.eval_expr(get_value, transaction, *a)
                    .and_then(|a_value| {
                        self.eval_expr(get_value, transaction, *b)
                            .map(|b_value| match op {
                                BinOp::Equal => {
                                    if a_value.is_equal(&b_value) {
                                        BitVecValue::new_true()
                                    } else {
                                        BitVecValue::new_false()
                                    }
                                }
                                BinOp::Concat => a_value.concat(&b_value),
                            })
                    })
            }
            Expr::Unary(UnaryOp::Not, e) => {
                self.eval_expr(get_value, transaction, *e).map(|v| v.not())
            }
            Expr::Slice(_, _, _) => todo!(),
        }
    }
}

/// returns a dut port symbol if the expression corresponds to one
fn as_dut_port_symbol(transaction: &Transaction, expr: ExprId) -> Option<SymbolId> {
    match &transaction[expr] {
        Expr::Sym(sym_id) => {
            // we assume that the only symbols are dut ports and arguments
            if as_arg(transaction, expr).is_none() {
                Some(*sym_id)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// returns argument and id if the expression corresponds to one
fn as_arg(transaction: &Transaction, expr: ExprId) -> Option<(usize, Arg)> {
    match &transaction[expr] {
        Expr::Sym(sym_id) => transaction
            .args
            .iter()
            .enumerate()
            .find(|(_, a)| a.symbol() == *sym_id)
            .map(|(i, a)| (i, *a)),
        _ => None,
    }
}

impl From<Transaction> for TransactionInfo {
    fn from(t: Transaction) -> Self {
        let next_stmt = t.next_stmt_mapping();
        Self {
            transaction: t,
            next_stmt,
        }
    }
}

#[derive(Debug)]
struct TransactionInfo {
    transaction: Transaction,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
}
