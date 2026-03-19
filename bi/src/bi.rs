// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::proto_trace::*;
use crate::signal_trace::*;
use baa::{BitVecMutOps, BitVecOps, BitVecValue, WidthInt};
use protocols::ir::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct BackwardsInterpreter<T: SignalTrace> {
    trace: T,
    transactions: Vec<ProtoInfo>,
    instance_id: u32,
    include_in_progress: bool,
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
        include_in_progress: bool,
    ) -> Self {
        let transactions: Vec<_> = transactions_and_symbols
            .enumerate()
            .map(|(proto_id, (t, sym))| {
                let next_stmt = t.next_stmt_mapping();
                ProtoInfo {
                    proto_id,
                    proto: t.clone(),
                    sym: sym.clone(),
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
            include_in_progress,
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

                // step trace
                if self.trace.step() == StepResult::Done {
                    if self.include_in_progress {
                        // at the end of the trace, we add unfinished transactions to the trace
                        for path in self.next.iter() {
                            let mut active = path.active.clone();
                            active.sort_by_key(|t| u32::MAX - t.start_step);
                            for thread in active {
                                self.traces.append(
                                    path.trace_id,
                                    thread_to_call(&self.transactions, thread, None),
                                );
                            }
                        }
                    }
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
                ThreadResult::RepeatLoop => {
                    let tid = thread.transaction_id;
                    let (a, b) = thread.exec_repeat_loop_branch(&tis[tid]);
                    (PathResult::Branch(vec![a, b]), None)
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
    arg_values: Vec<ArgValue>,
    pin_assignments: Vec<(StmtId, SymbolId, ExprId)>,
    has_forked: bool,
    step: u32,
    start_step: u32,
    failures: Vec<Failure>,
}

#[derive(Debug, Clone)]
enum ThreadResult {
    Ok,
    RepeatLoop,
    Step,
    Fork,
    FinalStepAndFork,
    FinalStep,
    Failed,
}

impl Thread {
    fn exec_repeat_loop_branch(self, ti: &ProtoInfo) -> (Thread, Thread) {
        let stmt = self.next_stmt.expect("");
        debug_assert!(
            matches!(&ti.proto[stmt], Stmt::RepeatLoop(_, _)),
            "repeat loop!"
        );
        let (body, arg_id) = if let Stmt::RepeatLoop(arg, body) = &ti.proto[stmt] {
            (*body, as_arg(&ti.proto, *arg).unwrap().0)
        } else {
            unreachable!(
                "this function may only be called when executing a repeat loop statement!"
            );
        };

        // if we take the repeat loop branch, we up the value
        let mut taken = self.clone();
        let arg_value = taken.arg_values[arg_id]
            .as_repeat()
            .expect("must be a uint arg");
        arg_value.increment_current_value();
        let value = arg_value.current_value();
        taken.name = format!("{}{value}?", taken.name);
        taken.next_stmt = Some(body);

        // of we do not take the branch, we jump after the loop
        let mut not_taken = self;
        let arg_value = not_taken.arg_values[arg_id]
            .as_repeat()
            .expect("must be a uint arg");
        let max_iter = arg_value.current_value();
        *arg_value = RepeatValue::Exactly(max_iter, 0);
        not_taken.name = format!("{}{max_iter}!", not_taken.name);
        not_taken.next_stmt = ti.next_stmt[&stmt];

        // we need to explore both versions of our thread
        (taken, not_taken)
    }

    fn exec_stmt(
        &mut self,
        ti: &ProtoInfo,
        get_value: &impl Fn(SymbolId) -> BitVecValue,
    ) -> ThreadResult {
        use ThreadResult::*;
        if let Some(stmt) = self.next_stmt {
            // println!("{:?}", &ti.proto[stmt]);
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
                    let assign_ok = self.check_assignments(ti, get_value);
                    self.step += 1;

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
                    assert!(self.step > 0, "[{}] Cannot fork at step zero!", self.name);
                    self.has_forked = true;
                    self.next_stmt = ti.next_stmt[&stmt];
                    Fork
                }
                Stmt::While(cond, body) => {
                    let cond_value = self
                        .eval_expr(get_value, &ti.proto, *cond)
                        .expect("while condition is always concrete");
                    self.next_stmt = if cond_value.is_true() {
                        Some(*body)
                    } else {
                        ti.next_stmt[&stmt]
                    };
                    Ok
                }
                Stmt::RepeatLoop(repetitions, body) => {
                    let arg_id = as_arg(&ti.proto, *repetitions)
                        .expect("repeat loop repetition count needs to be an argument")
                        .0;

                    let arg_value = self.arg_values[arg_id]
                        .as_repeat()
                        .expect("must be a repeat arg");

                    // check to see if the number of iterations is known
                    // in this case we essentially just have a for(i=0; i < max_iters; i++) loop
                    if let Some(max_iters) = arg_value.num_iters() {
                        if arg_value.current_value() < max_iters {
                            arg_value.increment_current_value();
                            self.next_stmt = Some(*body);
                        } else {
                            // this will make the current value overflow and go back to zero
                            arg_value.increment_current_value();
                            self.next_stmt = ti.next_stmt[&stmt]; // exit loop
                        }
                        Ok
                    } else {
                        // we do not actually know the correct number of steps, and we need to explore both possibilities
                        // this must happen outside of this method since it involves cloning the thread
                        RepeatLoop
                    }
                }
                Stmt::IfElse(cond, tru, fals) => {
                    let cond_value = self
                        .eval_expr(get_value, &ti.proto, *cond)
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
                    thread_local_step: self.step,
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
                if let ArgValue::Data(d) = &mut self.arg_values[arg_id] {
                    d.define_value(lhs_value);
                } else {
                    unreachable!("assignments/assert_eq must involve data values (bit vectors)!")
                }
                // println!(
                //     "[{}] Discovered that ?? = {}",
                //     self.name,
                //     lhs_value.to_bit_str()
                // );
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
            return self.arg_values[arg_id].get_known();
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
    sym: SymbolTable,
    next_stmt: FxHashMap<StmtId, Option<StmtId>>,
}

#[derive(Debug, Clone)]
enum ArgValue {
    Data(DataValue),
    Repeat(RepeatValue),
}

impl ArgValue {
    fn unknown(sym: &SymbolTable, arg: &Arg) -> Self {
        match sym[arg.symbol()].tpe() {
            Type::UnsignedInt => Self::Repeat(RepeatValue::default()),
            Type::BitVec(w) => Self::Data(DataValue::unknown(w)),
            Type::Struct(_) => unreachable!("args cannot be structs"),
            Type::Unknown => unreachable!("arg types are always known"),
        }
    }

    fn get_known(&self) -> Option<BitVecValue> {
        match self {
            ArgValue::Data(d) => d.get_known(),
            ArgValue::Repeat(RepeatValue::Exactly(v, _)) => {
                Some(BitVecValue::from_u64(*v as u64, 32))
            }
            ArgValue::Repeat(RepeatValue::AtLeast(_)) => None,
        }
    }

    fn as_repeat(&mut self) -> Option<&mut RepeatValue> {
        if let Self::Repeat(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
enum RepeatValue {
    AtLeast(u32),
    Exactly(u32, u32),
}

impl Default for RepeatValue {
    fn default() -> Self {
        Self::AtLeast(0)
    }
}

impl RepeatValue {
    fn current_value(&self) -> u32 {
        match self {
            RepeatValue::AtLeast(v) => *v,
            RepeatValue::Exactly(_, v) => *v,
        }
    }

    fn increment_current_value(&mut self) {
        match self {
            RepeatValue::AtLeast(v) => *v += 1,
            RepeatValue::Exactly(b, v) => {
                if *v + 1 == *b {
                    *v = 0;
                } else {
                    *v += 1;
                }
                debug_assert!(*v < *b);
            }
        }
    }

    fn num_iters(&self) -> Option<u32> {
        match self {
            RepeatValue::AtLeast(_) => None,
            RepeatValue::Exactly(b, _) => Some(*b),
        }
    }
}

#[derive(Debug, Clone)]
struct DataValue {
    value: BitVecValue,
    known: BitVecValue,
}

impl DataValue {
    fn unknown(width: WidthInt) -> Self {
        Self {
            value: BitVecValue::zero(width),
            known: BitVecValue::zero(width),
        }
    }

    fn get_known(&self) -> Option<BitVecValue> {
        if self.known.is_all_ones() {
            Some(self.value.clone())
        } else {
            None
        }
    }

    #[allow(dead_code)]
    fn bit_is_known(&self, bit: WidthInt) -> bool {
        self.known.is_bit_set(bit)
    }

    #[allow(dead_code)]
    fn define_bit(&mut self, bit: WidthInt, value: u8) {
        debug_assert!(!self.bit_is_known(bit));
        debug_assert!(bit < self.value.width());
        if value != 0 {
            self.value.set_bit(bit);
        }
        self.known.set_bit(bit);
    }

    fn define_value(&mut self, value: BitVecValue) {
        debug_assert_eq!(self.value.width(), value.width());
        self.value = value;
        self.known = BitVecValue::ones(self.value.width());
    }
}
