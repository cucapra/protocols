// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::signal_trace::{SignalTrace, StepResult};
use baa::BitVecValue;
use protocols::ir::*;
use rustc_hash::FxHashMap;

pub type ProtoTrace = Vec<(String, Vec<Option<BitVecValue>>)>;

pub struct BackwardsInterpreter<T: SignalTrace> {
    /// Active protocol execution traces
    executions: Vec<ExecutionContext>,
    trace: T,
    transactions: Vec<TransactionInfo>,
    instance_id: u32,
    step: u32,
}

impl<T: SignalTrace> BackwardsInterpreter<T> {
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

    pub fn step(&mut self) -> bool {
        let execs = std::mem::take(&mut self.executions);
        let mut failed = vec![];

        // step all possible execution paths
        for mut exec in execs {
            let r = exec.step(&self.transactions, &|sym| {
                self.trace.get(self.instance_id, sym)
            });
            match r {
                ExecResult::Ok => self.executions.push(exec),
                ExecResult::Failed => failed.push(exec),
                ExecResult::OkForked => {
                    // fork means that we need to _immediately_ start a new thread
                    for mut forked in exec.fork(self.transactions.iter()) {
                        match forked.step_new_thread(&self.transactions, &|sym| {
                            self.trace.get(self.instance_id, sym)
                        }) {
                            ExecResult::Ok => self.executions.push(forked),
                            ExecResult::OkForked => unreachable!("cannot fork in first step"),
                            ExecResult::Failed => failed.push(forked),
                        }
                    }
                }
            }
        }

        // make sure that at least one path is still active
        if self.executions.is_empty() {
            panic!(
                "{}: all executions failed. No matching execution trace found.\nFailed: {failed:?}",
                self.step
            );
        }

        let trace_done = self.trace.step() == StepResult::Done;
        self.step += 1;
        !trace_done
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

#[derive(Debug, Copy, Clone)]
enum ExecResult {
    Ok,
    OkForked,
    Failed,
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

        let mut any_forked = false;
        while let Some(mut thread) = active_threads.pop() {
            let (res, forked) = self.step_thread(transactions, get_value, &mut thread);
            assert!(
                !(any_forked && forked),
                "Two threads forking at the same step should be impossible!"
            );
            any_forked |= forked;
            match res {
                ExecThreadResult::Yield => {
                    next_threads.push(thread);
                }
                ExecThreadResult::Failed => {
                    failed.push(thread);
                }
                ExecThreadResult::Finished => {
                    // implicit fork at the end of a thread
                    if !thread.has_forked {
                        assert!(
                            !(any_forked && forked),
                            "Two threads forking at the same step should be impossible!"
                        );
                        any_forked |= forked;
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

        if !failed.is_empty() {
            ExecResult::Failed
        } else if any_forked {
            ExecResult::OkForked
        } else {
            ExecResult::Ok
        }
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
                todo!("should not happen")
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
                    if self.exec_equality(get_value, &transaction, thread, *lhs, *rhs) {
                        next_stmts[&stmt]
                    } else {
                        return (
                            ExecThreadResult::Failed,
                            thread.has_forked && !forked_before,
                        );
                    }
                }
                Stmt::Step => {
                    thread.next_stmt = next_stmts[&stmt];
                    thread.steps += 1;
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
                Stmt::While(_, _) => {
                    todo!("while")
                }
                Stmt::BoundedLoop(_, _) => {
                    todo!("repeat")
                }
                Stmt::IfElse(_, _, _) => {
                    todo!("if else")
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
        get_value: impl Fn(SymbolId) -> BitVecValue,
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
        get_value: impl Fn(SymbolId) -> BitVecValue,
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
            Expr::Binary(_, _, _) => todo!(),
            Expr::Unary(_, _) => todo!(),
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
                transaction_id: id,
                next_stmt: Some(t.transaction.body),
                arg_values: vec![None; t.transaction.args.len()],
                has_forked: false,
                steps: 0,
            });
            ctx
        })
    }
}

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
    transaction_id: usize,
    next_stmt: Option<StmtId>,
    arg_values: Vec<Option<BitVecValue>>,
    has_forked: bool,
    steps: u32,
}
