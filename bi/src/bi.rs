// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::signal_trace::{SignalTrace, StepResult};
use baa::{BitVecOps, BitVecValue};
use protocols::ir::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub type ProtoTrace = Vec<ProtoCall>;

#[derive(Debug, Clone)]
pub struct ProtoCall {
    pub name: String,
    pub start: u32,
    pub end: u32,
    pub args: Vec<Option<BitVecValue>>,
}

pub struct BackwardsInterpreter<T: SignalTrace> {
    trace: T,
    transactions: Vec<TransactionInfo>,
    instance_id: u32,
    step: u32,
    active: Vec<Path>,
    next: Vec<Path>,
    failed: Vec<Path>,
    traces: Traces,
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
        let mut traces = Traces::default();
        let active = Path::new(&mut traces).fork(transactions.iter(), &mut traces);

        Self {
            transactions,
            trace,
            instance_id,
            step,
            active,
            next: vec![],
            failed: vec![],
            traces,
        }
    }

    pub fn run(&mut self) -> BIResult {
        while self.exec() {}
        BIResult::Done
    }

    pub fn protocol_traces(&self) -> impl Iterator<Item = ProtoTrace> {
        self.traces.unique_traces().into_iter()
    }

    pub fn steps(&self) -> u32 {
        self.step
    }

    /// execute a single statement
    fn exec(&mut self) -> bool {
        if let Some(mut path) = self.active.pop() {
            // println!("{}", path.thread_string());

            // execute one path
            let (r, pc) = path.exec_stmt(&self.transactions, &|sym| {
                self.trace.get(self.instance_id, sym)
            });

            // append protocols that finish to trace
            if let Some(value) = pc {
                self.traces.append(path.trace_id, value);
            }

            match r {
                PathResult::Ok => {
                    debug_assert!(!path.failed());
                    self.active.push(path);
                }
                PathResult::Fork => {
                    let mut new_paths = path.fork(self.transactions.iter(), &mut self.traces);
                    debug_assert!(new_paths.iter().all(|p| !p.failed()));
                    self.active.append(&mut new_paths);
                }
                PathResult::FinishedStep => {
                    debug_assert!(
                        !path.active.is_empty()
                            && path.next.is_empty()
                            && path.step == self.step + 1,
                        "path should be ready to run the next step"
                    );
                    debug_assert!(!path.failed(), "{path:?}");
                    self.next.push(path);
                }
                PathResult::FinishedStepAndFork => {
                    debug_assert!(
                        // here `path.active` can be empty since we are forking off more threads
                        path.next.is_empty() && path.step == self.step + 1,
                        "path should be ready to run the next step"
                    );
                    debug_assert!(!path.failed(), "{path:?}");
                    let mut new_paths = path.fork(self.transactions.iter(), &mut self.traces);
                    self.next.append(&mut new_paths);
                }
                PathResult::Failed => {
                    debug_assert!(path.failed());
                    self.traces.remove(path.trace_id);
                    self.failed.push(path);
                }
            }
            true
        } else {
            // otherwise all paths must be finished
            debug_assert!(self.active.is_empty());
            debug_assert!(self.failed.iter().all(|p| p.failed()));
            let all_failed = self.next.is_empty();
            if all_failed {
                println!("show good error message when all paths fail");
                false // stop
            } else {
                // step trace
                if self.trace.step() == StepResult::Done {
                    return false;
                }
                // println!("----- Finished Step {}", self.step);
                // discard failed paths and prepare others for next step
                self.failed.clear();
                self.active.append(&mut self.next);
                self.step += 1;
                true
            }
        }
    }
}

/// An execution path.
#[derive(Debug, Clone)]
struct Path {
    trace_id: TraceId,
    active: Vec<Thread>,
    failed: Vec<Thread>,
    next: Vec<Thread>,
    step: u32,
    has_forked_this_step: bool,
    fork_next_step: bool,
}

#[derive(Debug, Clone)]
enum PathResult {
    Ok,
    Fork,
    Failed,
    FinishedStep,
    FinishedStepAndFork,
}

impl Path {
    fn new(traces: &mut Traces) -> Self {
        let trace_id = traces.empty();
        Self {
            trace_id,
            active: vec![],
            failed: vec![],
            next: vec![],
            step: 0,
            has_forked_this_step: false,
            fork_next_step: false,
        }
    }

    #[allow(dead_code)]
    fn thread_string(&self) -> String {
        let active = self
            .active
            .iter()
            .map(|t| t.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let next = self
            .next
            .iter()
            .map(|t| t.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let failed = self
            .failed
            .iter()
            .map(|t| t.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let status = if self.failed() {
            "F"
        } else if self.active.is_empty() {
            "S"
        } else {
            "A"
        };
        format!("[{status}] {failed} {active} --> {next}")
    }

    fn fork<'a>(
        self,
        transactions: impl Iterator<Item = &'a TransactionInfo>,
        traces: &mut Traces,
    ) -> Vec<Self> {
        debug_assert!(self.failed.is_empty());
        transactions
            .enumerate()
            .map(move |(id, t)| {
                let mut p = self.clone();
                if id > 0 {
                    // ensure every new path has a unique trace
                    p.trace_id = traces.fork(p.trace_id);
                }

                let t = Thread {
                    name: format!("{}@{}", t.transaction.name, self.step),
                    transaction_id: id,
                    next_stmt: Some(t.transaction.body),
                    arg_values: vec![None; t.transaction.args.len()],
                    has_forked: false,
                    steps: 0,
                    pin_assignments: vec![],
                    start_step: self.step,
                };
                p.active.push(t);
                p
            })
            .collect()
    }

    fn failed(&self) -> bool {
        !self.failed.is_empty()
    }

    fn exec_stmt(
        &mut self,
        tis: &[TransactionInfo],
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> (PathResult, Option<ProtoCall>) {
        // we need to always execute the oldest thread first in order to get the correct order
        // of transactions in our output trace (we want the oldest transaction to appear first in the trace)
        self.active.sort_by_key(|t| u32::MAX - t.start_step);
        if let Some(mut thread) = self.active.pop() {
            let r = thread.exec_stmt(&tis[thread.transaction_id], get_value);
            // println!("{r:?}");
            match r {
                ThreadResult::Failed => {
                    self.failed.push(thread);
                    (PathResult::Failed, None)
                }
                ThreadResult::Ok => {
                    self.active.push(thread);
                    (PathResult::Ok, None)
                }
                ThreadResult::Fork => {
                    assert!(!self.has_forked_this_step && !self.fork_next_step);
                    self.has_forked_this_step = true;
                    self.active.push(thread);
                    (PathResult::Fork, None)
                }
                ThreadResult::Step => {
                    self.next.push(thread);
                    (PathResult::Ok, None)
                }
                ThreadResult::FinalStep => {
                    (PathResult::Ok, Some(thread_to_call(tis, thread, self.step)))
                }
                ThreadResult::FinalStepAndFork => {
                    self.fork_next_step = true;
                    (PathResult::Ok, Some(thread_to_call(tis, thread, self.step)))
                }
            }
        } else {
            // finish step
            debug_assert!(!self.failed());
            self.step += 1;
            self.active.append(&mut self.next);
            if self.fork_next_step {
                self.fork_next_step = false;
                self.has_forked_this_step = true;
                (PathResult::FinishedStepAndFork, None)
            } else {
                self.has_forked_this_step = false;
                (PathResult::FinishedStep, None)
            }
        }
    }
}

fn thread_to_call(tis: &[TransactionInfo], thread: Thread, end: u32) -> ProtoCall {
    assert!(thread.next_stmt.is_none());
    let name = tis[thread.transaction_id].transaction.name.clone();
    let args = thread.arg_values;
    let start = thread.start_step;
    ProtoCall {
        name,
        args,
        start,
        end,
    }
}

#[derive(Debug, Clone)]
struct Thread {
    #[allow(dead_code)]
    name: String,
    transaction_id: usize,
    next_stmt: Option<StmtId>,
    arg_values: Vec<Option<BitVecValue>>,
    pin_assignments: Vec<(SymbolId, ExprId)>,
    has_forked: bool,
    steps: u32,
    start_step: u32,
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
    fn exec_stmt(
        &mut self,
        ti: &TransactionInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        use ThreadResult::*;
        if let Some(stmt) = self.next_stmt {
            // println!("{:?}", &ti.transaction[stmt]);
            match &ti.transaction[stmt] {
                Stmt::Block(stmt_ids) => {
                    self.next_stmt = stmt_ids.first().cloned();
                    Ok
                }
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    self.pin_assignments.push((*lhs, *rhs));
                    self.next_stmt = ti.next_stmt[&stmt];
                    Ok
                }
                Stmt::Step => {
                    self.next_stmt = ti.next_stmt[&stmt];
                    self.steps += 1;
                    let assign_ok = self.check_assignments(&ti.transaction, get_value);

                    match (assign_ok, self.next_stmt.is_none(), self.has_forked) {
                        // we found a constraint violation from the assignments
                        (false, _, _) => Failed,
                        // this is the last step in the protocol, and we have not forked yet
                        (true, true, false) => FinalStepAndFork,
                        // this is the last step in the protocol, but we already forked
                        (true, true, true) => FinalStep,
                        // there is more to execute and all assignment constraints passed
                        (true, false, _) => Step,
                    }
                }
                Stmt::Fork => {
                    self.has_forked = true;
                    self.next_stmt = ti.next_stmt[&stmt];
                    Fork
                }
                Stmt::While(cond, body) => {
                    let cond_value = self
                        .eval_expr(get_value, &&ti.transaction, *cond)
                        .expect("while condition is always concrete");
                    self.next_stmt = if cond_value.is_true() {
                        Some(*body)
                    } else {
                        ti.next_stmt[&stmt]
                    };
                    Ok
                }
                Stmt::RepeatLoop(repetitions, body) => {
                    let (arg_id, arg) = as_arg(&ti.transaction, *repetitions)
                        .expect("repeat loop repetition count needs to be an argument");

                    todo!("repeat {:?}", arg.symbol())
                }
                Stmt::IfElse(cond, tru, fals) => {
                    let cond_value = self
                        .eval_expr(get_value, &&ti.transaction, *cond)
                        .expect("if condition is always concrete");
                    self.next_stmt = if cond_value.is_true() {
                        Some(*tru)
                    } else {
                        Some(*fals)
                    };
                    Ok
                }
                Stmt::AssertEq(lhs, rhs) => {
                    let (port, other) = match (
                        as_dut_port_symbol(&ti.transaction, *lhs),
                        as_dut_port_symbol(&ti.transaction, *rhs),
                    ) {
                        (Some(port), _) => (port, *rhs),
                        (_, Some(port)) => (port, *lhs),
                        (None, None) => {
                            todo!("we currently expect one side of an assert_eq to be a port!")
                        }
                    };
                    self.next_stmt = ti.next_stmt[&stmt];
                    if self.exec_equality(get_value, &ti.transaction, port, other) {
                        Ok
                    } else {
                        Failed
                    }
                }
            }
        } else {
            unreachable!("should have finished with a step!")
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
                //     self.name,
                //     lhs_value.to_bit_str(),
                //     rhs_value.to_bit_str()
                // );
            }
            rhs_value == lhs_value
        } else {
            if let Some((arg_id, _arg)) = as_arg(&transaction, rhs) {
                debug_assert!(self.arg_values[arg_id].is_none());
                // println!(
                //     "[{}] Discovered that ?? = {}",
                //     self.name,
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

#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
struct TraceId(u32);

#[derive(Debug, Clone)]
struct TraceEntry {
    value: ProtoCall,
    prev: Option<u32>,
}

#[derive(Debug, Default)]
struct Traces {
    entries: Vec<TraceEntry>,
    tails: Vec<Option<u32>>,
}

impl Traces {
    fn append(&mut self, trace: TraceId, value: ProtoCall) {
        let entry_id = self.entries.len() as u32;
        let prev = self.tails.get(trace.0 as usize).cloned().flatten();
        self.entries.push(TraceEntry { value, prev });
        self.tails[trace.0 as usize] = Some(entry_id);
    }

    fn fork(&mut self, trace: TraceId) -> TraceId {
        let new_id = TraceId(self.tails.len() as u32);
        self.tails.push(self.tails[trace.0 as usize]);
        new_id
    }

    fn empty(&mut self) -> TraceId {
        let new_id = TraceId(self.tails.len() as u32);
        self.tails.push(None);
        new_id
    }

    fn remove(&mut self, trace: TraceId) {
        // TODO: remove any orphaned entries (GC!)
        self.tails[trace.0 as usize] = None;
    }

    fn unique_traces(&self) -> Vec<ProtoTrace> {
        let mut tails: Vec<_> = self.tails.iter().cloned().flatten().collect();
        tails.sort();
        tails.dedup();
        tails
            .into_iter()
            .map(|t| {
                let mut out = vec![];
                let mut t = Some(t);
                while let Some(entry_id) = t {
                    let entry = &self.entries[entry_id as usize];
                    out.push(entry.value.clone());
                    t = entry.prev;
                }
                out.reverse();
                out
            })
            .collect()
    }
}
