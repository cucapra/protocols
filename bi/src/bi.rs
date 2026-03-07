// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::signal_trace::{SignalTrace, StepResult};
use baa::{BitVecOps, BitVecValue};
use protocols::ir::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub type ProtoTrace = Vec<(String, Vec<Option<BitVecValue>>)>;

pub struct BackwardsInterpreter<T: SignalTrace> {
    /// Active protocol execution traces
    executions: Vec<ExecutionContext>,
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
    pub fn steps(&self) -> u32 {
        self.step
    }

    pub fn new(
        transactions_and_symbols: Vec<(Transaction, SymbolTable)>,
        trace: T,
        instance_id: u32,
    ) -> Self {
        let transactions: Vec<_> = transactions_and_symbols
            .into_iter()
            .map(|(t, _)| {
                let next_stmt = t.next_stmt_mapping();
                TransactionInfo {
                    transaction: t,
                    next_stmt,
                }
            })
            .collect();

        let step = 0;
        // create one execution context per transaction
        let executions = ExecutionContext::default()
            .fork(transactions.iter())
            .collect();

        Self {
            transactions,
            trace,
            executions,
            instance_id,
            step,
        }
    }

    pub fn step(&mut self) -> BIResult {
        let execs = std::mem::take(&mut self.executions);
        let mut failed = vec![];

        // step all possible execution paths
        for mut exec in execs {
            debug_assert!(!exec.threads.is_empty(), "lost all threads!");
            let r = exec.step(&self.transactions, &|sym| {
                self.trace.get(self.instance_id, sym)
            });
            match r {
                ExecResult::Ok => self.executions.push(exec),
                ExecResult::Failed => failed.push(exec),
                ExecResult::OkForked(_thread) => {
                    // fork means that we need to _immediately_ start a new thread
                    for mut forked in exec.fork(self.transactions.iter()) {
                        match forked.step_new_thread(&self.transactions, &|sym| {
                            self.trace.get(self.instance_id, sym)
                        }) {
                            ExecResult::Ok => self.executions.push(forked),
                            ExecResult::OkForked(_) => unreachable!("cannot fork in first step"),
                            ExecResult::OkDelayedFork(_thread) => {
                                // execute forked threads together with all other threads in the next step
                                for forked in forked.fork(self.transactions.iter()) {
                                    self.executions.push(forked);
                                }
                            }
                            ExecResult::Failed => failed.push(forked),
                        }
                    }
                }
                ExecResult::OkDelayedFork(_thread) => {
                    // execute forked threads together with all other threads in the next step
                    for forked in exec.fork(self.transactions.iter()) {
                        self.executions.push(forked);
                    }
                }
            }
        }

        // make sure that at least one path is still active
        if self.executions.is_empty() {
            self.executions = failed; // just in order to extract the trace
            BIResult::Fail
        } else {
            let trace_done = self.trace.step() == StepResult::Done;
            self.step += 1;
            // println!("[step] {trace_done}");
            if trace_done {
                BIResult::Done
            } else {
                BIResult::Ok
            }
        }
    }

    pub fn protocol_traces(&self) -> impl Iterator<Item = ProtoTrace> {
        self.executions.iter().map(|e| e.trace.clone())
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

#[derive(Debug, Default, Clone)]
struct ExecutionContext {
    threads: Vec<Thread>,
    trace: ProtoTrace,
}

#[derive(Debug, Clone)]
enum ExecResult {
    Ok,
    OkForked(String),
    OkDelayedFork(String), // happens when there is a thread that finishes without having forked
    Failed,
}

impl ExecResult {
    fn is_ok(&self) -> bool {
        matches!(
            self,
            ExecResult::Ok | ExecResult::OkForked(_) | ExecResult::OkDelayedFork(_)
        )
    }
    fn forked(&self) -> bool {
        matches!(self, ExecResult::OkForked(_) | ExecResult::OkDelayedFork(_))
    }
}

impl ExecutionContext {
    fn step(
        &mut self,
        transactions: &[TransactionInfo],
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ExecResult {
        let mut active_threads = std::mem::take(&mut self.threads);
        let mut next_threads = vec![];
        let mut finished = vec![];
        let mut failed = vec![];

        let mut status = ExecResult::Ok;
        while let Some(mut thread) = active_threads.pop() {
            let (res, forked) = self.step_thread(transactions, get_value, &mut thread);
            if forked {
                assert!(
                    !status.forked(),
                    "Two threads forking at the same step should be impossible!"
                );
                if status.is_ok() {
                    status = ExecResult::OkForked(thread.name.clone())
                }
            }

            match res {
                ExecThreadResult::Yield => {
                    next_threads.push(thread);
                }
                ExecThreadResult::Failed => {
                    status = ExecResult::Failed;
                    failed.push(thread);
                }
                ExecThreadResult::Finished => {
                    // implicit fork at the end of a thread
                    if !thread.has_forked {
                        assert!(
                            !status.forked(),
                            "Two threads forking at the same step should be impossible!"
                        );
                        if status.is_ok() {
                            status = ExecResult::OkDelayedFork(thread.name.clone())
                        }
                    }
                    finished.push(thread);
                }
            }
        }
        debug_assert!(active_threads.is_empty());
        self.threads = next_threads;

        for thread in finished {
            let name = transactions[thread.transaction_id].transaction.name.clone();
            // TODO: check to make sure that there are no older threads in flight!
            self.trace.push((name, thread.arg_values));
        }

        status
    }

    // used after forking, steps only the last pushed thread
    fn step_new_thread(
        &mut self,
        transactions: &[TransactionInfo],
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ExecResult {
        let mut thread = self.threads.pop().unwrap();
        assert_eq!(thread.steps, 0);
        let (res, forked) = self.step_thread(transactions, get_value, &mut thread);
        assert!(!forked, "Cannot fork in first step!");
        match res {
            ExecThreadResult::Yield => {
                self.threads.push(thread);
                ExecResult::Ok
            }
            ExecThreadResult::Failed => ExecResult::Failed,
            ExecThreadResult::Finished => {
                assert!(!thread.has_forked);
                ExecResult::OkDelayedFork(thread.name.clone())
            }
        }
    }

    fn step_thread(
        &self,
        transactions: &[TransactionInfo],
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        thread: &mut Thread,
    ) -> (ExecThreadResult, bool) {
        let mut pc = thread.next_stmt;
        let transaction = &transactions[thread.transaction_id].transaction;
        let next_stmts = &transactions[thread.transaction_id].next_stmt;
        let forked_before = thread.has_forked;
        while let Some(stmt) = pc {
            pc = match &transaction[stmt] {
                Stmt::Block(stmt_ids) => stmt_ids.first().cloned(),
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    thread.pin_assignments.push((*lhs, *rhs));
                    next_stmts[&stmt]
                }
                Stmt::Step => {
                    thread.next_stmt = next_stmts[&stmt];
                    thread.steps += 1;

                    // check assignments
                    let mut pins_assigned = FxHashSet::default();
                    let assignments = std::mem::take(&mut thread.pin_assignments);
                    for (pin, expr) in assignments.into_iter().rev() {
                        if !pins_assigned.contains(&pin) {
                            pins_assigned.insert(pin);
                            if !self.exec_equality(get_value, transaction, thread, pin, expr) {
                                // early exit on failure
                                return (
                                    ExecThreadResult::Failed,
                                    thread.has_forked && !forked_before,
                                );
                            } else if !matches!(transaction[expr], Expr::DontCare) {
                                // assignment sticks around for the next step
                                thread.pin_assignments.push((pin, expr));
                            }
                        }
                    }

                    let r = if thread.next_stmt.is_none() {
                        ExecThreadResult::Finished
                    } else {
                        ExecThreadResult::Yield
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
                    let (arg_id, arg) = as_arg(transaction, *repetitions)
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
                        as_dut_port_symbol(&transaction, *lhs),
                        as_dut_port_symbol(&transaction, *rhs),
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
                            ExecThreadResult::Failed,
                            thread.has_forked && !forked_before,
                        );
                    }
                }
            };
        }
        debug_assert!(pc.is_none());
        panic!("Protocols need to end in a step!")
    }

    /// used for both assert_eq and assignments
    fn exec_equality(
        &self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        transaction: &Transaction,
        thread: &mut Thread,
        lhs: SymbolId,
        rhs: ExprId,
    ) -> bool {
        // a DontCare imposes no constraints and thus there is nothing to learn, nothing to check
        if matches!(transaction[rhs], Expr::DontCare) {
            return true;
        }

        let lhs_value = get_value(lhs);
        if let Some(rhs_value) = self.eval_expr(get_value, transaction, thread, rhs) {
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
                debug_assert!(thread.arg_values[arg_id].is_none());
                // println!(
                //     "[{}] Discovered that {} = {}",
                //     transaction.name,
                //     transactions[thread.transaction_id].symbol_table[lhs].name(),
                //     lhs_value.to_bit_str()
                // );
                thread.arg_values[arg_id] = Some(lhs_value);
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
        thread: &Thread,
        expr: ExprId,
    ) -> Option<BitVecValue> {
        if let Some((arg_id, _)) = as_arg(transaction, expr) {
            return thread.arg_values[arg_id].clone();
        }
        match &transaction[expr] {
            Expr::Const(value) => Some(value.clone()),
            Expr::Sym(dut_port) => Some(get_value(*dut_port)),
            Expr::DontCare => None,
            Expr::Binary(op, a, b) => {
                self.eval_expr(get_value, transaction, thread, *a)
                    .and_then(|a_value| {
                        self.eval_expr(get_value, transaction, thread, *b)
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
            Expr::Unary(UnaryOp::Not, e) => self
                .eval_expr(get_value, transaction, thread, *e)
                .map(|v| v.not()),
            Expr::Slice(_, _, _) => todo!(),
        }
    }

    fn fork<'a>(
        &self,
        transactions: impl Iterator<Item = &'a TransactionInfo>,
    ) -> impl Iterator<Item = ExecutionContext> {
        transactions.enumerate().map(move |(id, t)| {
            let mut ctx = (*self).clone();
            ctx.threads.push(Thread {
                name: t.transaction.name.clone(),
                transaction_id: id,
                next_stmt: Some(t.transaction.body),
                arg_values: vec![None; t.transaction.args.len()],
                has_forked: false,
                steps: 0,
                pin_assignments: vec![],
            });
            ctx
        })
    }
}

#[derive(Debug, Copy, Clone)]
enum ExecThreadResult {
    Yield,
    Failed,
    Finished,
}

#[derive(Debug)]
struct TransactionInfo {
    transaction: Transaction,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
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
