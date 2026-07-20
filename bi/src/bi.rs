// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::constraints::ArgValue;
use crate::proto_trace::*;
use crate::signal_trace::*;
use baa::{BitVecOps, BitVecValue, WidthInt};
use protocols::frontend::ast::*;
use protocols::frontend::serialize::serialize_expr;
use protocols::frontend::symbol::{Arg, SymbolId, SymbolTable};
use rustc_hash::{FxHashMap, FxHashSet};

pub struct BackwardsInterpreter {
    protos: Vec<ProtoInfo>,
    instance_id: u32,
    include_in_progress: bool,
    step: u32,
    active: Vec<Path>,
    next: Vec<Path>,
    failed: Vec<Path>,
    traces: Traces,
    state: BIState,
}

pub type Failures = Vec<(TraceId, Vec<Failure>)>;

#[derive(Debug, Clone, PartialEq)]
enum BIResult {
    Ok,
    Step,
    Fail(Failures),
}
#[derive(Debug, Clone, PartialEq)]
pub enum BIState {
    Ready,
    AtEndOfStep,
    Finished,
    Failed(Failures),
}

impl BackwardsInterpreter {
    pub fn new(
        sym: &SymbolTable,
        protos: &[Protocol],
        instance_id: u32,
        include_in_progress: bool,
    ) -> Self {
        let protos: Vec<_> = protos
            .iter()
            .cloned()
            .enumerate()
            .map(|(proto_id, mut proto)| {
                let next_stmt = proto.next_stmt_mapping();
                let pin_symbols: Vec<_> = proto.dut_pins(sym).collect();
                let pin_exprs = pin_symbols
                    .into_iter()
                    .map(|pin| (pin, proto.ctx.e(Expr::Sym(pin))))
                    .collect();
                ProtoInfo {
                    proto_id,
                    proto,
                    sym: sym.clone(),
                    next_stmt,
                    pin_exprs,
                }
            })
            .collect();
        let step = 0;
        let mut traces = Traces::default();
        let active = Path::new(&mut traces).fork(protos.iter(), &mut traces);

        Self {
            protos,
            instance_id,
            include_in_progress,
            step,
            active,
            next: vec![],
            failed: vec![],
            traces,
            state: BIState::Ready,
        }
    }

    pub fn protocol_traces(&self) -> &Traces {
        &self.traces
    }

    pub fn has_failed(&self) -> bool {
        self.failures().is_some()
    }

    pub fn failures(&self) -> Option<&Failures> {
        if let BIState::Failed(f) = &self.state {
            Some(f)
        } else {
            None
        }
    }

    pub fn exec_step<T: SignalTrace>(&mut self, trace: &T) -> std::result::Result<(), Failures> {
        match self.state.clone() {
            BIState::Ready => {}
            BIState::AtEndOfStep => {
                self.active.append(&mut self.next);
                self.step += 1;
                self.state = BIState::Ready;
            }
            BIState::Finished => {
                unreachable!("Should never call exec_step on a finished BI!")
            }
            BIState::Failed(f) => {
                return Err(f);
            }
        }
        // println!("-------{}: {:?}", self.step, self.state);
        loop {
            match self.exec_stmt(trace) {
                BIResult::Ok => {}
                BIResult::Step => {
                    self.state = BIState::AtEndOfStep;
                    return Ok(());
                }
                BIResult::Fail(f) => {
                    self.state = BIState::Failed(f.clone());
                    return Err(f);
                }
            }
        }
    }

    /// execute a single statement
    fn exec_stmt<T: SignalTrace>(&mut self, trace: &T) -> BIResult {
        if let Some(mut path) = self.active.pop() {
            // println!("{}", path.thread_string());

            // execute one path
            let (r, pc) = path.exec_stmt(&self.protos, &|sym| {
                // let value = trace.get(self.instance_id, sym);
                // println!("{sym:?} = {} : bv<{}>", value.to_dec_str(), value.width());
                // value
                trace.get(self.instance_id, sym)
            });

            // println!("path.exec_stmt(...) -> {r:?}");

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
                    let mut new_paths = path.fork(self.protos.iter(), &mut self.traces);
                    debug_assert!(new_paths.iter().all(|p| !p.failed()));
                    self.active.append(&mut new_paths);
                }
                PathResult::Branch(new_threads) => {
                    self.active
                        .extend(new_threads.into_iter().enumerate().map(|(id, new_t)| {
                            let mut p = path.clone();
                            p.active.push(new_t);
                            if id > 0 {
                                // ensure every new path has a unique trace
                                p.trace_id = self.traces.fork(p.trace_id);
                            }
                            p
                        }))
                }
                PathResult::FinishedStep => {
                    debug_assert!(path.failed.is_empty(), "failed thread");
                    debug_assert!(
                        path.next.len() + path.active.len() > 0,
                        "No active or next threads!"
                    );
                    debug_assert!(
                        !path.active.is_empty()
                            && path.next.is_empty()
                            && path.step == self.step + 1,
                        "path should be ready to run the next step. active: {}, next: {}, path.step: {}, global.step + 1: {}",
                        path.active.len(),
                        path.next.len(),
                        path.step,
                        self.step + 1
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
                    let mut new_paths = path.fork(self.protos.iter(), &mut self.traces);
                    self.next.append(&mut new_paths);
                }
                PathResult::Failed => {
                    debug_assert!(path.failed());
                    self.failed.push(path);
                }
            }
            BIResult::Ok
        } else {
            // println!("BI: Finished step {}. Traces failed={}, active={}", self.step, self.failed.len(), self.next.len());
            // for f in self.failed.iter().chain(self.next.iter()) {
            //     println!(" - {}", f.thread_string());
            // }
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

                BIResult::Step
            }
        }
    }

    /// Called after the last step.
    pub fn finish(&mut self) {
        debug_assert!(matches!(self.state, BIState::AtEndOfStep));
        if self.include_in_progress {
            // at the end of the trace, we add unfinished transactions to the trace
            for path in self.next.iter() {
                let mut active = path.active.clone();
                active.sort_by_key(|t| u32::MAX - t.start_step);
                for thread in active {
                    self.traces
                        .append(path.trace_id, thread_to_call(&self.protos, thread, None));
                }
            }
        }
        self.state = BIState::Finished;
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
    Branch(Vec<Thread>),
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
            .map(|t| format!("{}@{:?}", t.name.as_str(), t.next_stmt))
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

                let arg_values = t
                    .proto
                    .args
                    .iter()
                    .map(|a| ArgValue::unknown(&t.sym, a))
                    .collect();

                let t = Thread {
                    name: format!("{}@{}", t.proto.name, self.step),
                    transaction_id: id,
                    next_stmt: Some(t.proto.body),
                    arg_values,
                    has_forked: false,
                    step: 0,
                    pin_assignments: vec![],
                    start_step: self.step,
                    failures: vec![],
                    loop_iter_counts: vec![],
                    effectful_stmt_in_step: false,
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
            // println!("thread.exec_stmt(...) -> {r:?}");
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
                    assert!(
                        !self.has_forked_this_step,
                        "another thread already forked in the same thread!"
                    );
                    assert!(!self.fork_next_step);
                    self.has_forked_this_step = true;
                    self.active.push(thread);
                    (PathResult::Fork, None)
                }
                ThreadResult::Step => {
                    self.next.push(thread);
                    (PathResult::Ok, None)
                }
                ThreadResult::RepeatLoop(iters) => {
                    let tid = thread.transaction_id;
                    let (a, b) = thread.exec_repeat_loop_branch(&tis[tid], iters);
                    (PathResult::Branch(vec![a, b]), None)
                }
                ThreadResult::ForkIsLast(loop_stmt) => {
                    let tid = thread.transaction_id;
                    let (a, b) = thread.exec_is_last_branch(&tis[tid], loop_stmt);
                    (PathResult::Branch(vec![a, b]), None)
                }
                ThreadResult::FinishedWithoutStep => {
                    // When this happens, it means that we executed some "effectless" statements
                    // in this step and the transaction essentially ended the step before.
                    let res = if !thread.has_forked {
                        // implicit fork
                        assert!(
                            !self.has_forked_this_step,
                            "another thread already forked in the same thread!"
                        );
                        assert!(!self.fork_next_step);
                        self.has_forked_this_step = true;
                        PathResult::Fork
                    } else {
                        PathResult::Ok
                    };
                    let proto_call = thread_to_call(tis, thread, Some(self.step - 1));
                    (res, Some(proto_call))
                }
                ThreadResult::FinalStep => (
                    PathResult::Ok,
                    Some(thread_to_call(tis, thread, Some(self.step))),
                ),
                ThreadResult::FinalStepAndFork => {
                    self.fork_next_step = true;
                    (
                        PathResult::Ok,
                        Some(thread_to_call(tis, thread, Some(self.step))),
                    )
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

fn thread_to_call(tis: &[ProtoInfo], thread: Thread, end: Option<u32>) -> ProtoCall {
    assert!(end.is_none() || thread.next_stmt.is_none());
    let name = tis[thread.transaction_id].proto.name.clone();
    let args = thread.arg_values.iter().map(|a| a.get_known()).collect();
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
    /// repeat/for loop statement, iteration count, for-in loops also have a loop variable that can
    /// be used inside the loop
    loop_iter_counts: Vec<(StmtId, u64, Option<SymbolId>)>,
    arg_values: Vec<ArgValue>,
    pin_assignments: Vec<(StmtId, SymbolId, ExprId)>,
    has_forked: bool,
    step: u32,
    start_step: u32,
    failures: Vec<Failure>,
    // keeps track of whether an effectful statement like assign or assert has been encountered in
    // this step
    effectful_stmt_in_step: bool,
}

#[derive(Debug, Clone)]
enum ThreadResult {
    Ok,
    // fork a repeat loop, argument is the number of iterations already taken
    RepeatLoop(u64),
    // fork to resolve is last with for-in/repeat loop statement id
    ForkIsLast(StmtId),
    Step,
    Fork,
    FinalStepAndFork,
    FinalStep,
    FinishedWithoutStep,
    Failed,
}

impl Thread {
    fn exec_repeat_loop_branch(self, ti: &ProtoInfo, iters: u64) -> (Thread, Thread) {
        let stmt = self.next_stmt.expect("");
        let (body, arg_expr, maybe_loop_var) = match ti.proto[stmt].clone() {
            Stmt::RepeatLoop(arg, body) => (body, arg, None),
            Stmt::ForInLoop(loop_var, arg, body) => (body, arg, Some(loop_var)),
            _ => unreachable!(
                "We should only get here if the current statement is a repeat of for-in loop"
            ),
        };
        let arg_id = as_arg(&ti.proto, arg_expr).unwrap().0;

        // if we take the repeat loop branch, we just keep the count and go into the body
        let mut taken = self.clone();
        taken.name = format!("{}{}?", taken.name, iters + 1);
        taken.next_stmt = Some(body);
        taken.loop_iter_counts.push((stmt, iters, maybe_loop_var));
        if maybe_loop_var.is_some() {
            // we need to add one more element to the argument
            taken.arg_values[arg_id]
                .as_seq_mut()
                .expect("must be a seq")
                .increment_unknown_len();
        }

        // of we do not take the branch, we jump after the loop and freeze the value
        let mut not_taken = self;
        if maybe_loop_var.is_none() {
            // repeat loop
            not_taken.arg_values[arg_id]
                .as_scalar_mut()
                .expect("must be a scalar")
                .define_value(BitVecValue::from_u64(iters, 64));
        } else {
            // for-in loop
            not_taken.arg_values[arg_id]
                .as_seq_mut()
                .expect("must be a seq")
                .freeze_len();
        }
        not_taken.name = format!("{}{iters}!", not_taken.name);
        not_taken.next_stmt = ti.next_stmt[&stmt];

        // we need to explore both versions of our thread
        (taken, not_taken)
    }

    fn exec_is_last_branch(mut self, ti: &ProtoInfo, loop_stmt_id: StmtId) -> (Thread, Thread) {
        match ti.proto[loop_stmt_id].clone() {
            Stmt::RepeatLoop(_arg, _) => todo!("add support for repeat loop"),
            Stmt::ForInLoop(_, arg, _) => {
                let arg_id = as_arg(&ti.proto, arg).unwrap().0;

                // for making is_last true, we just need to flip the current (minimum) length to be
                // the known, fixed length
                let mut is_last_thread = self.clone();
                is_last_thread.name = format!("{}L", self.name);
                is_last_thread.arg_values[arg_id]
                    .as_seq_mut()
                    .unwrap()
                    .freeze_len();

                // to make is_last true, we up the minimum length by one
                self.arg_values[arg_id]
                    .as_seq_mut()
                    .unwrap()
                    .increment_unknown_len();
                (is_last_thread, self)
            }
            _ => unreachable!(
                "We should only get here if the current statement is a repeat of for-in loop"
            ),
        }
    }

    fn exec_stmt(
        &mut self,
        ti: &ProtoInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        use ThreadResult::*;
        if let Some(stmt) = self.next_stmt {
            // println!(
            //     "[{}]: {:?} ({:?})",
            //     self.name, &ti.proto[stmt], self.loop_iter_counts
            // );
            match &ti.proto[stmt] {
                Stmt::Block(stmt_ids) if stmt_ids.is_empty() => {
                    self.next_stmt = ti.next_stmt[&stmt];
                    Ok
                }
                Stmt::Block(stmt_ids) => {
                    self.next_stmt = stmt_ids.first().cloned();
                    Ok
                }
                Stmt::Assign(lhs, rhs) => {
                    // we apply all pin assignments at the end of a step
                    self.pin_assignments.push((stmt, *lhs, *rhs));
                    self.next_stmt = ti.next_stmt[&stmt];
                    self.effectful_stmt_in_step = true;
                    Ok
                }
                Stmt::Step => {
                    self.next_stmt = ti.next_stmt[&stmt];
                    let assign_ok = self.check_assignments(ti, get_value);
                    self.step += 1;
                    self.effectful_stmt_in_step = false;

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
                    if self.step > 0 {
                        self.has_forked = true;
                        self.next_stmt = ti.next_stmt[&stmt];
                        self.effectful_stmt_in_step = true;
                        Fork
                    } else {
                        eprintln!("[{}] Cannot fork at step zero!", self.name);
                        std::process::exit(1);
                    }
                }
                Stmt::While(cond, body) => {
                    let cond_value = self
                        .eval_expr(get_value, ti, *cond)
                        .expect("while condition is always concrete");
                    self.next_stmt = if cond_value.is_true() {
                        Some(*body)
                    } else {
                        ti.next_stmt[&stmt]
                    };
                    Ok
                }
                Stmt::RepeatLoop(repetitions, body) => {
                    // how often have we executed this thread on the current execution path
                    let iters = self.get_inner_loop_iters(stmt);

                    // retrieve num iteration argument
                    let max_iter_arg_id = as_arg(&ti.proto, *repetitions)
                        .expect("repeat loop repetition count needs to be an argument")
                        .0;
                    let max_iter_value = self.arg_values[max_iter_arg_id]
                        .as_scalar_mut()
                        .expect("must be a scalar arg");

                    // do we know the maximum number of iterations?
                    if let Some(max_iters) = max_iter_value.get_known() {
                        let max_iters = max_iters.to_u64().unwrap();
                        if iters == max_iters {
                            self.next_stmt = ti.next_stmt[&stmt]; // exit loop
                        } else {
                            assert!(iters < max_iters, "{iters} >= {max_iters}");
                            self.loop_iter_counts.push((stmt, iters, None));
                            self.next_stmt = Some(*body);
                        }
                        Ok
                    } else {
                        // we do not actually know the correct number of steps, and we need to explore both possibilities
                        // this must happen outside of this method since it involves cloning the thread
                        RepeatLoop(iters)
                    }
                }
                Stmt::ForInLoop(loop_var_id, seq_expr, body) => {
                    // how often have we executed this thread on the current execution path
                    let iters = self.get_inner_loop_iters(stmt);

                    // retrieve sequence argument
                    let arg_id = as_arg(&ti.proto, *seq_expr)
                        .expect("for-in sequence argument needs to be an argument to the protocol")
                        .0;
                    let arg_value = self.arg_values[arg_id]
                        .as_seq_mut()
                        .expect("must be a repeat arg");

                    // minimum number of iterations
                    let min_len = arg_value.min_len();

                    // println!(
                    //     "iters={iters}, min={min_len:?}, len={:?}",
                    //     arg_value.get_known_len()
                    // );

                    // do we know the maximum number of iterations?
                    if let Some(max_iters) = arg_value.get_known_len() {
                        debug_assert!(max_iters >= min_len);
                        if iters == max_iters {
                            self.next_stmt = ti.next_stmt[&stmt]; // exit loop
                        } else {
                            assert!(iters < max_iters);
                            self.loop_iter_counts
                                .push((stmt, iters, Some(*loop_var_id)));
                            self.next_stmt = Some(*body);
                        }
                        Ok
                    } else if iters < min_len {
                        // there is no branching, we need to iterate!
                        self.loop_iter_counts
                            .push((stmt, iters, Some(*loop_var_id)));
                        self.next_stmt = Some(*body);
                        Ok
                    } else {
                        // we do not actually know the correct number of steps, and we need to explore both possibilities
                        // this must happen outside of this method since it involves cloning the thread
                        RepeatLoop(iters)
                    }
                }
                Stmt::IfElse(cond, tru, fals) => match self.eval_expr(get_value, ti, *cond) {
                    ExprValue::Known(cond_value) => {
                        self.next_stmt = if cond_value.is_true() {
                            Some(*tru)
                        } else {
                            Some(*fals)
                        };
                        Ok
                    }
                    ExprValue::DependsOnIsLast(stmt) => ForkIsLast(stmt),
                    other => todo!("if condition is {other:?}"),
                },
                Stmt::AssertEq(lhs, rhs) => {
                    self.effectful_stmt_in_step = true;
                    self.next_stmt = ti.next_stmt[&stmt];
                    if let Some(fail) = self.exec_equality(get_value, ti, stmt, *lhs, *rhs) {
                        self.failures.push(fail);
                        Failed
                    } else {
                        Ok
                    }
                }
            }
        } else {
            assert!(
                !self.effectful_stmt_in_step,
                "should not finish without a final step!"
            );
            FinishedWithoutStep
        }
    }

    fn get_inner_loop_iters(&mut self, stmt: StmtId) -> u64 {
        // have we executed this loop before?
        if let Some((check_stmt_id, iters, _)) = self.loop_iter_counts.last().cloned()
            && check_stmt_id == stmt
        {
            self.loop_iter_counts.pop().unwrap();
            iters + 1
        } else {
            0
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
            // println!("{:?}, {}, {:?}", &ti.proto[stmt], ti.sym[pin].full_name(&ti.sym), &ti.proto[expr]);

            // only the final assignment to a pin matters
            if !pins_assigned.contains(&pin) {
                pins_assigned.insert(pin);
                let pin_expr = ti.pin_exprs[&pin];
                if let Some(fail) = self.exec_equality(get_value, ti, stmt, pin_expr, expr) {
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
    /// we try out best to treat lhs and rhs the same since assert_eq is commutative
    fn exec_equality(
        &mut self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        ti: &ProtoInfo,
        stmt: StmtId,
        lhs: ExprId,
        rhs: ExprId,
    ) -> Option<Failure> {
        // a DontCare imposes no constraints and thus there is nothing to learn, nothing to check
        if matches!(ti.proto[rhs], Expr::DontCare) || matches!(ti.proto[lhs], Expr::DontCare) {
            return None;
        }

        let a = self.eval_expr(get_value, ti, lhs);
        let b = self.eval_expr(get_value, ti, rhs);

        match (a, b) {
            (ExprValue::Known(a), ExprValue::Known(b)) => {
                if a.is_equal(&b) {
                    None
                } else {
                    // println!(
                    //     "[{}] found a disagreement: {} =/= {}",
                    //     self.name,
                    //     lhs_value.to_bit_str(),
                    //     rhs_value.to_bit_str()
                    // );
                    Some(Failure {
                        thread_local_step: self.step,
                        proto_id: ti.proto_id,
                        thread_name: self.name.clone(),
                        stmt,
                        a,
                        b,
                    })
                }
            }
            (ExprValue::UnknownArg(arg_id, None, _msb, lsb), ExprValue::Known(value))
            | (ExprValue::Known(value), ExprValue::UnknownArg(arg_id, None, _msb, lsb)) => {
                self.arg_values[arg_id]
                    .as_scalar_mut()
                    .expect("assignments/assert_eq must involve data values (bit vectors)!")
                    .define_bits(value, lsb);
                None
            }
            (ExprValue::UnknownArg(arg_id, Some(index), _msb, lsb), ExprValue::Known(value))
            | (ExprValue::Known(value), ExprValue::UnknownArg(arg_id, Some(index), _msb, lsb)) => {
                self.arg_values[arg_id]
                    .as_seq_mut()
                    .expect("assignments/assert_eq must involve data values (bit vectors)!")
                    .define_bits_at(index, value, lsb);
                None
            }
            (a, b) => panic!(
                "At least one value of an assert_eq is unknown. What should we do?\nassert_eq({}, {})\n{a:?} ==? {b:?}",
                serialize_expr(&ti.proto.ctx, &ti.sym, &lhs),
                serialize_expr(&ti.proto.ctx, &ti.sym, &rhs)
            ),
        }
    }

    fn eval_expr(
        &self,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
        ti: &ProtoInfo,
        expr: ExprId,
    ) -> ExprValue {
        match &ti.proto[expr] {
            Expr::Sym(sym_id) => {
                if ti.sym[sym_id].is_arg() {
                    let arg_index = sym_as_arg(&ti.proto, *sym_id).unwrap().0;
                    let arg = self.arg_values[arg_index]
                        .as_scalar()
                        .expect("only scalar arguments should ever be evaluated");
                    arg.get_known()
                        .map(ExprValue::Known)
                        .unwrap_or(ExprValue::UnknownArg(arg_index, None, arg.width() - 1, 0))
                } else if ti.sym[sym_id].is_port() {
                    ExprValue::Known(get_value(*sym_id))
                } else if ti.sym[sym_id].is_loop_var() {
                    let (stmt, iter, _) = *self.loop_iter_counts.iter().rev().find(|(_, _, a)| *a == Some(*sym_id)).expect("failed to find loop variable. Are we outside of the corresponding for-in loop?");
                    if let Stmt::ForInLoop(check_sym_id, seq_expr, _) = ti.proto[stmt] {
                        debug_assert_eq!(check_sym_id, *sym_id);
                        // retrieve sequence argument
                        let arg_id = as_arg(&ti.proto, seq_expr)
                            .expect(
                                "for-in sequence argument needs to be an argument to the protocol",
                            )
                            .0;
                        let arg_value = self.arg_values[arg_id]
                            .as_seq()
                            .expect("must be a repeat arg");
                        arg_value
                            .get_known_at(iter)
                            .map(ExprValue::Known)
                            .unwrap_or(ExprValue::UnknownArg(
                                arg_id,
                                Some(iter),
                                arg_value.element_width() - 1,
                                0,
                            ))
                    } else {
                        unreachable!("Only for-in loops can have loop variables!");
                    }
                } else {
                    unreachable!("unknown symbol kind!")
                }
            }
            Expr::Const(value) => ExprValue::Known(value.clone()),
            Expr::DontCare => ExprValue::DontCare,
            Expr::Binary(op, a, b) => {
                let a = self.eval_expr(get_value, ti, *a);
                let b = self.eval_expr(get_value, ti, *b);
                match (a, b) {
                    (ExprValue::Known(a), ExprValue::Known(b)) => {
                        let res = match op {
                            BinOp::Equal => {
                                if a.is_equal(&b) {
                                    BitVecValue::new_true()
                                } else {
                                    BitVecValue::new_false()
                                }
                            }
                            BinOp::Concat => a.concat(&b),
                            BinOp::Add => a.add(&b),
                            BinOp::And => a.and(&b),
                        };
                        ExprValue::Known(res)
                    }
                    // special case for addition with zero
                    (ExprValue::Known(zero), other) | (other, ExprValue::Known(zero))
                        if matches!(op, BinOp::Add) && zero.is_zero() =>
                    {
                        other
                    }
                    // special case: concatenating two continuous slices of the same argument
                    (
                        ExprValue::UnknownArg(a_id, a_index, a_msb, a_lsb),
                        ExprValue::UnknownArg(b_id, b_index, b_msb, b_lsb),
                    ) if matches!(op, BinOp::Concat)
                        && (a_id == b_id)
                        && (a_index == b_index)
                        && (a_lsb == b_msb + 1) =>
                    {
                        ExprValue::UnknownArg(a_id, a_index, a_msb, b_lsb)
                    }
                    (ExprValue::DontCare, _) | (_, ExprValue::DontCare) => ExprValue::DontCare,
                    (ExprValue::Unknown | ExprValue::UnknownArg(..), _)
                    | (_, ExprValue::Unknown | ExprValue::UnknownArg(..)) => ExprValue::Unknown,
                    (ExprValue::DependsOnIsLast(s), _) | (_, ExprValue::DependsOnIsLast(s)) => {
                        ExprValue::DependsOnIsLast(s)
                    }
                }
            }
            Expr::Unary(UnaryOp::Not, e) => match self.eval_expr(get_value, ti, *e) {
                ExprValue::Known(v) => ExprValue::Known(v.not()),
                other => other,
            },
            Expr::Slice(e, msb, lsb) => match self.eval_expr(get_value, ti, *e) {
                ExprValue::Known(v) => ExprValue::Known(v.slice(*msb, *lsb)),
                ExprValue::UnknownArg(id, index, _, lsb_old) => {
                    ExprValue::UnknownArg(id, index, msb + lsb_old, lsb + lsb_old)
                }
                other => other,
            },
            Expr::IsLastIteration => {
                // The iter_count is the number of _completed_ iterations.
                // So, on the first iteration: `iter_count == 0`
                let (stmt, iter_count, _) = *self.loop_iter_counts.last().unwrap();
                match &ti.proto[stmt] {
                    Stmt::ForInLoop(_, seq_expr, _) => {
                        // retrieve sequence argument
                        let arg_id = as_arg(&ti.proto, *seq_expr)
                            .expect(
                                "for-in sequence argument needs to be an argument to the protocol",
                            )
                            .0;
                        let arg_value = self.arg_values[arg_id]
                            .as_seq()
                            .expect("must be a repeat arg");
                        // 1) Is the number of iterations known precisely?
                        if let Some(max_iter) = arg_value.get_known_len() {
                            if max_iter == iter_count + 1 {
                                ExprValue::Known(BitVecValue::new_true())
                            } else {
                                ExprValue::Known(BitVecValue::new_false())
                            }
                        }
                        // 2) is there a lower bound to the number of iterations
                        else if arg_value.min_len() > iter_count + 1 {
                            ExprValue::Known(BitVecValue::new_false())
                        }
                        // 3) otherwise, it could be either, meaning that we will have to branch
                        else {
                            ExprValue::DependsOnIsLast(stmt)
                        }
                    }
                    Stmt::RepeatLoop(_, _) => {
                        todo!("implement is_last for repeat loops!");
                    }
                    other => unreachable!("{:?}", other),
                }
            }
            Expr::IterCount(width) => {
                let (_, iter_count, _) = self
                    .loop_iter_counts
                    .last()
                    .expect("is_last() must be inside of a loop!");
                let mask = mask64(*width);
                let value = BitVecValue::from_u64(*iter_count & mask, *width);
                ExprValue::Known(value)
            }
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

#[derive(Debug, Clone)]
enum ExprValue {
    Known(BitVecValue),
    DontCare,
    Unknown,
    /// arg_id, optional index for sequence args, msb, lsb
    UnknownArg(usize, Option<u64>, u32, u32),
    DependsOnIsLast(StmtId),
}

impl ExprValue {
    fn expect(self, msg: &str) -> BitVecValue {
        if let ExprValue::Known(v) = self {
            v
        } else {
            panic!("{self:?} is not known! {}", msg)
        }
    }
}

/// returns argument and id if the expression corresponds to one
fn as_arg(transaction: &Protocol, expr: ExprId) -> Option<(usize, Arg)> {
    match &transaction[expr] {
        Expr::Sym(sym_id) => sym_as_arg(transaction, *sym_id),
        _ => None,
    }
}

fn sym_as_arg(transaction: &Protocol, sym_id: SymbolId) -> Option<(usize, Arg)> {
    transaction
        .args
        .iter()
        .enumerate()
        .find(|(_, a)| a.symbol() == sym_id)
        .map(|(i, a)| (i, *a))
}

#[derive(Debug)]
struct ProtoInfo {
    proto_id: usize,
    proto: Protocol,
    sym: SymbolTable,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
    pin_exprs: FxHashMap<SymbolId, ExprId>,
}
