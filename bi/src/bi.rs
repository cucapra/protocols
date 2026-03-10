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

        Self {
            transactions,
            trace,
            instance_id,
            step,
        }
    }

    pub fn run(&mut self) -> BIResult {
        let mut paths = Path::default().fork(self.transactions.iter(), false);
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
}

#[derive(Debug, Clone)]
enum PathResult {
    Fork,
    StepDone,
    Failed,
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

    fn exec(
        &mut self,
        ti: &TransactionInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> PathResult {
        if let Some(mut t) = self.active.pop() {
            match t.exec(ti, get_value) {
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
            PathResult::StepDone
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
    StepAndFork,
    Finished,
    Failed,
}

impl Thread {
    fn exec(
        &mut self,
        ti: &TransactionInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        if let Some(stmt) = self.next_stmt {
            let (next_stmt, result) = match &ti.transaction[stmt] {
                Stmt::Block(stmt_ids) => stmt_ids.first().cloned(),
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    self.pin_assignments.push((*lhs, *rhs));
                    ti.next_stmt[&stmt]
                }
                Stmt::Step => {
                    self.next_stmt = ti.next_stmt[&stmt];
                    self.steps += 1;
                    let assign_ok = self.check_assignments(&ti.transaction, get_value);

                    let r = if thread.next_stmt.is_none() {
                        crate::bi2::ExecThreadResult::Finished
                    } else {
                        crate::bi2::ExecThreadResult::Yield
                    };
                    return (r, thread.has_forked && !forked_before);
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
