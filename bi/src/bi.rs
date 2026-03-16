// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::proto_trace::*;
use crate::signal_trace::*;
use baa::{BitVecOps, BitVecValue};
use protocols::ir::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct BackwardsInterpreter<T: SignalTrace> {
    trace: T,
    transactions: Vec<ProtoInfo>,
    instance_id: u32,
    step: u32,
    active: Vec<Path>,
    next: Vec<Path>,
    failed: Vec<Path>,
    traces: Traces,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BIResult {
    Ok,
    Done,
    Fail(Vec<(TraceId, Vec<Failure>)>),
}

impl<T: SignalTrace> BackwardsInterpreter<T> {
    pub fn new<'a>(
        transactions_and_symbols: impl Iterator<Item = &'a (Transaction, SymbolTable)>,
        trace: T,
        instance_id: u32,
    ) -> Self {
        let transactions: Vec<_> = transactions_and_symbols
            .enumerate()
            .map(|(proto_id, (t, _))| {
                let next_stmt = t.next_stmt_mapping();
                ProtoInfo {
                    proto_id,
                    proto: t.clone(),
                    next_stmt,
                }
            })
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

    pub fn step_to_ns(&self, logical_step: u32) -> String {
        self.trace.step_to_ns(logical_step)
    }

    pub fn run(&mut self) -> BIResult {
        let mut r = self.exec_stmt();
        while r == BIResult::Ok {
            r = self.exec_stmt();
        }
        r
    }

    pub fn protocol_traces(&self) -> &Traces {
        &self.traces
    }

    /// execute a single statement
    fn exec_stmt(&mut self) -> BIResult {
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
                    self.failed.push(path);
                }
            }
            BIResult::Ok
        } else {
            // otherwise all paths must be finished
            debug_assert!(self.active.is_empty());
            debug_assert!(self.failed.iter().all(|p| p.failed()));
            let all_failed = self.next.is_empty();
            if all_failed {
                let failures = self
                    .failed
                    .iter()
                    .map(|p| {
                        (
                            p.trace_id,
                            p.failed
                                .iter()
                                .flat_map(|t| t.failures.iter())
                                .cloned()
                                .collect(),
                        )
                    })
                    .collect();
                BIResult::Fail(failures)
            } else {
                // discard failed paths and prepare others for next step
                for thread in self.failed.drain(..) {
                    // now, we can discard the traces of failed paths
                    self.traces.remove(thread.trace_id);
                }

                // step trace
                if self.trace.step() == StepResult::Done {
                    BIResult::Done
                } else {
                    self.active.append(&mut self.next);
                    self.step += 1;
                    BIResult::Ok
                }
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
        transactions: impl Iterator<Item = &'a ProtoInfo>,
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
                    name: format!("{}@{}", t.proto.name, self.step),
                    transaction_id: id,
                    next_stmt: Some(t.proto.body),
                    arg_values: vec![None; t.proto.args.len()],
                    has_forked: false,
                    step: 0,
                    pin_assignments: vec![],
                    start_step: self.step,
                    failures: vec![],
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
        tis: &[ProtoInfo],
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

fn thread_to_call(tis: &[ProtoInfo], thread: Thread, end: u32) -> ProtoCall {
    assert!(thread.next_stmt.is_none());
    let name = tis[thread.transaction_id].proto.name.clone();
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
    pin_assignments: Vec<(StmtId, SymbolId, ExprId)>,
    has_forked: bool,
    step: u32,
    start_step: u32,
    failures: Vec<Failure>,
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
        ti: &ProtoInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        use ThreadResult::*;
        if let Some(stmt) = self.next_stmt {
            // println!("{:?}", &ti.transaction[stmt]);
            match &ti.proto[stmt] {
                Stmt::Block(stmt_ids) => {
                    self.next_stmt = stmt_ids.first().cloned();
                    Ok
                }
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    self.pin_assignments.push((stmt, *lhs, *rhs));
                    self.next_stmt = ti.next_stmt[&stmt];
                    Ok
                }
                Stmt::Step => {
                    self.next_stmt = ti.next_stmt[&stmt];
                    self.step += 1;
                    let assign_ok = self.check_assignments(ti, get_value);

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
                        .eval_expr(get_value, &&ti.proto, *cond)
                        .expect("while condition is always concrete");
                    self.next_stmt = if cond_value.is_true() {
                        Some(*body)
                    } else {
                        ti.next_stmt[&stmt]
                    };
                    Ok
                }
                Stmt::RepeatLoop(repetitions, body) => {
                    let (arg_id, arg) = as_arg(&ti.proto, *repetitions)
                        .expect("repeat loop repetition count needs to be an argument");

                    todo!("repeat {:?}", arg.symbol())
                }
                Stmt::IfElse(cond, tru, fals) => {
                    let cond_value = self
                        .eval_expr(get_value, &&ti.proto, *cond)
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
                        as_dut_port_symbol(&ti.proto, *lhs),
                        as_dut_port_symbol(&ti.proto, *rhs),
                    ) {
                        (Some(port), _) => (port, *rhs),
                        (_, Some(port)) => (port, *lhs),
                        (None, None) => {
                            todo!("we currently expect one side of an assert_eq to be a port!")
                        }
                    };
                    self.next_stmt = ti.next_stmt[&stmt];

                    if let Some(fail) = self.exec_equality(get_value, ti, stmt, port, other) {
                        self.failures.push(fail);
                        Failed
                    } else {
                        Ok
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
        ti: &ProtoInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> bool {
        let mut pins_assigned = FxHashSet::default();
        let assignments = std::mem::take(&mut self.pin_assignments);
        // go from last assignment to first
        for (stmt, pin, expr) in assignments.into_iter().rev() {
            // only the final assignment to a pin matters
            if !pins_assigned.contains(&pin) {
                pins_assigned.insert(pin);
                if let Some(fail) = self.exec_equality(get_value, ti, stmt, pin, expr) {
                    self.failures.push(fail);
                } else if !matches!(ti.proto[expr], Expr::DontCare) {
                    // assignment sticks around for the next step
                    self.pin_assignments.push((stmt, pin, expr));
                }
            }
        }
        self.failures.is_empty()
    }

    /// used for both assert_eq and assignments
    fn exec_equality(
        &mut self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        ti: &ProtoInfo,
        stmt: StmtId,
        lhs: SymbolId,
        rhs: ExprId,
    ) -> Option<Failure> {
        // a DontCare imposes no constraints and thus there is nothing to learn, nothing to check
        if matches!(ti.proto[rhs], Expr::DontCare) {
            return None;
        }

        let lhs_value = get_value(lhs);
        if let Some(rhs_value) = self.eval_expr(get_value, &ti.proto, rhs) {
            if rhs_value != lhs_value {
                // println!(
                //     "[{}] found a disagreement: {} =/= {}",
                //     self.name,
                //     lhs_value.to_bit_str(),
                //     rhs_value.to_bit_str()
                // );
                Some(Failure {
                    step: self.step,
                    proto_id: ti.proto_id,
                    thread_name: self.name.clone(),
                    stmt,
                    a: lhs_value,
                    b: rhs_value,
                })
            } else {
                None
            }
        } else {
            if let Some((arg_id, _arg)) = as_arg(&ti.proto, rhs) {
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
            None
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

#[derive(Debug)]
struct ProtoInfo {
    proto_id: usize,
    proto: Transaction,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
}
