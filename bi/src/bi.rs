// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::signal_trace::{SignalTrace, StepResult};
use baa::{BitVecOps, BitVecValue};
use patronus::mc::SmtModelCheckerOptions;
use protocols::ir::{Arg, Dir, Expr, ExprId, Stmt, StmtId, SymbolId, SymbolTable, Transaction};
use protocols::parser::Rule::assert_eq;
use protocols::scheduler::NextStmtMap;
use rustc_hash::FxHashMap;

pub struct BackwardsInterpreter<T: SignalTrace> {
    threads: Vec<Thread>,
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
            .map(|(t, s)| {
                let next_stmt = t.next_stmt_mapping();
                TransactionInfo {
                    transaction: t,
                    symbol_table: s,
                    next_stmt,
                }
            })
            .collect();

        let step = 0;
        // create one thread per transaction
        let threads = fork(transactions.iter(), step).collect();

        Self {
            transactions,
            trace,
            threads,
            instance_id,
            step,
        }
    }

    pub fn step(&mut self) -> bool {
        let mut active_threads = std::mem::take(&mut self.threads);
        let mut next_threads = vec![];
        let mut finished = vec![];
        let mut failed = vec![];

        while let Some(mut thread) = active_threads.pop() {
            match self.exec_thread(&mut thread) {
                ExecThreadResult::Yield => {
                    next_threads.push(thread);
                }
                ExecThreadResult::Failed => {
                    failed.push(thread);
                }
                ExecThreadResult::Finished(forked) => {
                    finished.push(thread);
                    if forked {
                        active_threads.extend(fork(self.transactions.iter(), self.step));
                    }
                }
            }
        }
        debug_assert!(active_threads.is_empty());

        if !finished.is_empty() {
            todo!("deal with finished threads")
        }
        if !failed.is_empty() {
            todo!("deal with failed threads!")
        }

        self.threads = next_threads;
        let trace_done = self.trace.step() == StepResult::Done;
        let threads_done = self.threads.is_empty();
        let more_to_do = !trace_done && !threads_done;
        self.step += 1;
        println!("[step]");
        more_to_do
    }

    fn exec_thread(&self, thread: &mut Thread) -> ExecThreadResult {
        let mut pc = thread.next_stmt;
        let transaction = &self.transactions[thread.transaction_id].transaction;
        let next_stmts = &self.transactions[thread.transaction_id].next_stmt;
        let mut forked = false;
        while let Some(stmt) = pc {
            pc = match &transaction[stmt] {
                Stmt::Block(stmt_ids) => stmt_ids.first().cloned(),
                Stmt::Assign(lhs, rhs) => {
                    if self.exec_equality(&transaction, thread, *lhs, *rhs) {
                        next_stmts[&stmt]
                    } else {
                        return ExecThreadResult::Failed;
                    }
                }
                Stmt::Step => {
                    thread.next_stmt = next_stmts[&stmt];
                    return ExecThreadResult::Yield;
                }
                Stmt::Fork => {
                    forked = true;
                    next_stmts[&stmt]
                }
                Stmt::While(_, _) => {
                    todo!("while")
                }
                Stmt::IfElse(_, _, _) => {
                    todo!("if else")
                }
                Stmt::AssertEq(lhs, rhs) => {
                    let (port, other) = match (
                        self.as_dut_port_symbol(&transaction, *lhs),
                        self.as_dut_port_symbol(&transaction, *rhs),
                    ) {
                        (Some(port), _) => (port, *rhs),
                        (_, Some(port)) => (port, *lhs),
                        (None, None) => {
                            todo!("we currently expect one side of an assert_eq to be a port!")
                        }
                    };
                    if self.exec_equality(&transaction, thread, port, other) {
                        next_stmts[&stmt]
                    } else {
                        return ExecThreadResult::Failed;
                    }
                }
            };
        }
        debug_assert!(pc.is_none());
        ExecThreadResult::Finished(forked)
    }

    /// returns a dut port symbol if the expression corresponds to one
    fn as_dut_port_symbol(&self, transaction: &Transaction, expr: ExprId) -> Option<SymbolId> {
        match &transaction[expr] {
            Expr::Sym(sym_id) => {
                // we assume that the only symbols are dut ports and arguments
                if self.as_arg(transaction, expr).is_none() {
                    Some(*sym_id)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// returns argument and id if the expression corresponds to one
    fn as_arg(&self, transaction: &Transaction, expr: ExprId) -> Option<(usize, Arg)> {
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

    /// used for both assert_eq and assignments
    fn exec_equality(
        &self,
        transaction: &Transaction,
        thread: &mut Thread,
        lhs: SymbolId,
        rhs: ExprId,
    ) -> bool {
        // a DontCare imposes no constraints and thus there is nothing to learn, nothing to check
        if matches!(transaction[rhs], Expr::DontCare) {
            return true;
        }

        let lhs_value = self.trace.get(self.instance_id, lhs);
        if let Some(rhs_value) = self.eval_expr(transaction, thread, rhs) {
            if rhs_value != lhs_value {
                println!(
                    "[{}] found a disagreement: {} =/= {}",
                    transaction.name,
                    lhs_value.to_bit_str(),
                    rhs_value.to_bit_str()
                );
            }
            rhs_value == lhs_value
        } else {
            if let Some((arg_id, arg)) = self.as_arg(&transaction, rhs) {
                debug_assert!(thread.arg_values[arg_id].is_none());
                println!(
                    "[{}] Discovered that {} = {}",
                    transaction.name,
                    self.transactions[thread.transaction_id].symbol_table[lhs].name(),
                    lhs_value.to_bit_str()
                );
                thread.arg_values[arg_id] = Some(lhs_value);
            } else {
                todo!()
            }
            true
        }
    }

    fn eval_expr(
        &self,
        transaction: &Transaction,
        thread: &Thread,
        expr: ExprId,
    ) -> Option<BitVecValue> {
        if let Some((arg_id, _)) = self.as_arg(transaction, expr) {
            return thread.arg_values[arg_id].clone();
        }
        match &transaction[expr] {
            Expr::Const(value) => Some(value.clone()),
            Expr::Sym(dut_port) => Some(self.trace.get(self.instance_id, *dut_port)),
            Expr::DontCare => None,
            Expr::Binary(_, _, _) => todo!(),
            Expr::Unary(_, _) => todo!(),
            Expr::Slice(_, _, _) => todo!(),
        }
    }
}

enum ExecThreadResult {
    Yield,
    Failed,
    Finished(bool),
}

fn fork<'a>(
    transactions: impl Iterator<Item = &'a TransactionInfo>,
    start_step: u32,
) -> impl Iterator<Item = Thread> {
    transactions.enumerate().map(move |(id, t)| Thread {
        start_step,
        transaction_id: id,
        next_stmt: Some(t.transaction.body),
        arg_values: vec![None; t.transaction.args.len()],
    })
}

struct TransactionInfo {
    transaction: Transaction,
    symbol_table: SymbolTable,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
}

struct Thread {
    start_step: u32,
    transaction_id: usize,
    next_stmt: Option<StmtId>,
    arg_values: Vec<Option<BitVecValue>>,
}

impl Thread {
    fn run(&mut self) {}
}
