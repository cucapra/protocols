// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Graph-IR based reconstructor implementation.

// - build custom runner, we might want to generate results on the fly
// - we do not need to deal with the possibility of multiple traces
// - group transitions and actions by guard
// - can we save the guard evaluation history in order to decide which one to evaluate first?
// - is there maybe even a way to evaluate guards in parallel?
// - different than the existing bi, we should be able to never allocate during execution
// - we could define an array that contains all relevant values from the trace
//   and then compile expressions to byte code that contains the concrete indices

use crate::TraceFormat;
use baa::BitVecOps;
use bi::signal_trace::{PortMap, SignalValues};
use patronus::expr::{
    Context, Expr, ExprRef, SerializableIrNode, Simplifier, SparseExprMap, TypeCheck, WidthInt,
};
use protocols::frontend::ast::Protocol;
use protocols::frontend::symbol::SymbolKind::AutomatonState;
use protocols::frontend::symbol::{Arg, SymbolId, SymbolTable, Type};
use protocols::ir::joint_automaton::ProtocolId;
use protocols::ir::joint_monitor::{InstanceId, JointMonitorAutomaton};
use protocols::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use rustc_hash::FxHashMap;
use std::io::Write;

pub struct GraphBi<O: Write> {
    // static during execution
    bad_state: usize,
    states: Vec<ExecState>,
    // updated during execution
    regs: Regs,
    expr: ExprEval,
    step: u32,
    current_state: usize,
    // generated output
    mon: TraceMonitor<O>,
}

impl<O: Write> GraphBi<O> {
    pub fn new(
        st: &SymbolTable,
        ctx: &mut Context,
        port_map: &PortMap,
        monitor: JointMonitorAutomaton,
        show_graph: bool,
        mut out: TraceMonitor<O>,
    ) -> Self {
        if show_graph {
            println!("{}", monitor.to_dot_string(ctx, st));
        }

        let mut c = Compiler::default();
        c.compile(st, ctx, &monitor, port_map);
        let max_instances = monitor.control.bank_counts.iter().cloned().max().unwrap();
        out.init(st, &monitor.protocols, max_instances).unwrap();

        Self {
            current_state: monitor.control.graph.entry.as_u32() as usize,
            states: c.states,
            expr: c.expr.into(),
            regs: Regs::new(c.regs, c.heads),
            bad_state: monitor.bad_state.as_u32() as usize,
            mon: out,
            step: 0,
        }
    }

    pub fn has_failed(&self) -> bool {
        self.current_state == self.bad_state
    }

    pub fn exec_step(&mut self, values: SignalValues) -> std::io::Result<()> {
        if self.current_state != self.bad_state {
            self.current_state = self.exec_state(self.current_state, values)?;
            self.step += 1;
        }
        Ok(())
    }

    pub fn finish(mut self) -> std::io::Result<O> {
        writeln!(self.mon.out, "}}")?;
        Ok(self.mon.out)
    }
}

impl<O: Write> GraphBi<O> {
    fn exec_state(&mut self, state_id: usize, pin_values: SignalValues) -> std::io::Result<usize> {
        let state = &self.states[state_id];
        self.expr
            .eval_many(&state.unique_guards, &pin_values, &self.regs);

        // eval actions based on guards
        for (guard, act) in &state.acts {
            let guard = self.expr.eval(*guard, &pin_values, &self.regs);
            if guard != 0 {
                match act.clone() {
                    ExecAct::InternalAssertFalse => {
                        panic!("Internal assertion failed! State {}", self.current_state)
                    }
                    ExecAct::AssignReg(idx, instance, value) => {
                        let value = self.expr.eval(value, &pin_values, &self.regs);
                        self.regs.write(idx, instance, value);
                    }
                    ExecAct::AssertEq(lhs, rhs) => {
                        let lhs = self.expr.eval(lhs, &pin_values, &self.regs);
                        let rhs = self.expr.eval(rhs, &pin_values, &self.regs);
                        let is_ok = lhs == rhs;
                        if !is_ok {
                            panic!("assertion failed");
                        }
                    }
                    ExecAct::Finish(instance) => {
                        let instance = self.regs.eval_instance_id(instance);
                        self.mon.finish(instance, self.step)?;
                    }
                    ExecAct::Start(instance) => {
                        let instance = self.regs.eval_instance_id(instance);
                        self.mon.start(instance, self.step);
                    }
                    ExecAct::IncrHead(proto_id, amount) => {
                        self.regs.incr_head(proto_id, amount);
                    }
                    ExecAct::LearnedParam(instance, arg_idx, expr) => {
                        let value = self.expr.eval(expr, &pin_values, &self.regs);
                        let instance = self.regs.eval_instance_id(instance);
                        self.mon.learn_param(instance, arg_idx, value, self.step);
                    }
                }
            }
        }

        // calc next state based in guards:
        let next = state
            .trans
            .iter()
            .find(|(g, _)| self.expr.eval(*g, &pin_values, &self.regs) != 0)
            .cloned()
            .unwrap()
            .1 as usize;

        // invalidate expression cache
        self.expr.clear_cache();

        Ok(next)
    }
}

type Word = u64;

struct Regs {
    /// per protocol head counters
    heads: Vec<(usize, usize)>,
    /// other registers
    regs: Vec<Word>,
}

impl Regs {
    fn new(regs: Vec<Word>, heads: Vec<(usize, usize)>) -> Self {
        Self { heads, regs }
    }

    #[inline]
    fn incr_head(&mut self, proto_id: ProtocolId, amount: usize) {
        let (old, count) = self.heads[proto_id];
        self.heads[proto_id].0 = (old + amount) % count;
    }

    #[inline]
    fn read(&self, idx: usize, instance: InstanceId) -> Word {
        self.regs[self.reg_idx(idx, instance)].clone()
    }

    #[inline]
    fn write(&mut self, idx: usize, instance: InstanceId, value: Word) {
        let final_idx = self.reg_idx(idx, instance);
        self.regs[final_idx] = value;
    }

    #[inline]
    fn reg_idx(&self, idx: usize, instance: InstanceId) -> usize {
        let instance = self.eval_instance_id(instance);
        idx + instance.1
    }

    #[inline]
    fn eval_instance_id(&self, id: InstanceId) -> InstanceId {
        let (proto_id, base_instance) = id;
        let (head, count) = self.heads[proto_id];
        let instance = (base_instance + head) % count;
        (proto_id, instance)
    }
}

struct ExprEval {
    expr: Vec<ExecExpr>,
    cache: Vec<Option<Word>>,
    /// keep todo buffer around to avoid allocations
    todo: Vec<ExecExprId>,
}

impl From<Vec<ExecExpr>> for ExprEval {
    fn from(expr: Vec<ExecExpr>) -> Self {
        let cache = vec![None; expr.len()];
        Self {
            expr,
            cache,
            todo: Vec::with_capacity(1024),
        }
    }
}

impl ExprEval {
    fn clear_cache(&mut self) {
        for e in self.cache.iter_mut() {
            *e = None;
        }
    }

    fn eval_many(&mut self, expressions: &[ExecExprId], pin_values: &SignalValues, regs: &Regs) {
        debug_assert!(self.todo.is_empty());
        let mut todo = std::mem::take(&mut self.todo);
        todo.extend_from_slice(expressions);

        while let Some(expr_id) = todo.pop() {
            if self.cache[usize::from(expr_id)].is_none() {
                let new_expr = match self.expr[usize::from(expr_id)].clone() {
                    ExecExpr::Lit(v) => Some(v),
                    ExecExpr::Reg(idx, instance) => Some(regs.read(idx, instance)),
                    ExecExpr::DutPin(idx) => Some(pin_values[idx].to_u64().unwrap()),
                    ExecExpr::Not(e) if let Some(e) = self.cache[usize::from(e)] => Some(!e),
                    ExecExpr::Not(e) => {
                        todo.push(expr_id);
                        todo.push(e);
                        None
                    }
                    ExecExpr::Slice(e, hi, lo) if let Some(e) = self.cache[usize::from(e)] => {
                        let width = hi - lo + 1;
                        let mask = (1u64 << width) - 1;
                        Some((e >> lo) & mask)
                    }
                    ExecExpr::Slice(e, ..) => {
                        todo.push(expr_id);
                        todo.push(e);
                        None
                    }
                    ExecExpr::Bin(op, a, b, mask) => {
                        match (self.cache[usize::from(a)], self.cache[usize::from(b)]) {
                            (Some(a), Some(b)) => Some(match op {
                                BOp::And => a & b,
                                BOp::Or => a | b,
                                BOp::Xor => a ^ b,
                                BOp::Equal => {
                                    if a == b {
                                        1
                                    } else {
                                        0
                                    }
                                }
                                BOp::GreaterEqual => {
                                    if a >= b {
                                        1
                                    } else {
                                        0
                                    }
                                }
                                BOp::Add => (a + b) & mask,
                                BOp::Sub => (a - b) & mask,
                                BOp::Concat => a << mask & b,
                            }),
                            (None, Some(_)) => {
                                todo.push(expr_id);
                                todo.push(a);
                                None
                            }
                            (Some(_), None) => {
                                todo.push(expr_id);
                                todo.push(b);
                                None
                            }
                            (None, None) => {
                                todo.push(expr_id);
                                todo.push(a);
                                todo.push(b);
                                None
                            }
                        }
                    }
                    ExecExpr::Ite(cond, tru, fals) => {
                        if let Some(cond) = self.cache[usize::from(cond)] {
                            if cond == 0 {
                                let val = self.cache[usize::from(fals)];
                                if val.is_none() {
                                    todo.push(expr_id);
                                    todo.push(fals);
                                }
                                val.clone()
                            } else {
                                let val = self.cache[usize::from(tru)];
                                if val.is_none() {
                                    todo.push(expr_id);
                                    todo.push(tru);
                                }
                                val.clone()
                            }
                        } else {
                            todo.push(expr_id);
                            todo.push(cond);
                            None
                        }
                    }
                };
                self.cache[usize::from(expr_id)] = new_expr;
            }
        }

        debug_assert!(todo.is_empty());
        std::mem::swap(&mut todo, &mut self.todo);
    }

    #[inline]
    fn eval(&mut self, e: ExecExprId, pin_values: &SignalValues, regs: &Regs) -> Word {
        if let Some(e) = &self.cache[usize::from(e)] {
            e.clone()
        } else {
            self.eval_many(&[e], pin_values, regs);
            self.cache[usize::from(e)].clone().unwrap()
        }
    }
}

#[derive(Debug)]
pub struct TraceMonitor<O: Write> {
    out: O,
    format: TraceFormat,
    proto_names: Vec<String>,
    proto_ignore: Vec<bool>,
    transactions: Vec<Transaction>,
    max_instances: usize,
}

#[derive(Debug, Default, Clone)]
struct Transaction {
    start: u32,
    active: bool,
    args: Vec<ArgValue>,
}

#[derive(Debug, Clone)]
enum ArgValue {
    Scalar(Word),
    Seq(Vec<Word>),
}

impl ArgValue {
    fn empty(st: &SymbolTable, arg: &Arg) -> Self {
        match st[arg.symbol()].tpe() {
            Type::UnsignedInt => Self::Scalar(0),
            Type::BitVec(w) => {
                assert!(w <= Word::BITS);
                Self::Scalar(0)
            }
            Type::Seq(_) => Self::Seq(vec![]),
            Type::Tuple(_) => todo!("tuple"),
            Type::Struct(_) | Type::Unknown => unreachable!(),
        }
    }

    #[inline]
    fn clear(&mut self) {
        match self {
            ArgValue::Scalar(s) => *s = 0,
            ArgValue::Seq(s) => s.clear(),
        }
    }

    #[inline]
    fn learn(&mut self, value: Word) {
        match self {
            ArgValue::Scalar(s) => *s = value,
            ArgValue::Seq(s) => s.push(value),
        }
    }

    #[inline]
    fn serialize(&self, out: &mut impl Write, format: &TraceFormat) -> std::io::Result<()> {
        match self {
            ArgValue::Scalar(v) => serialize_bit_vec(v, out, format),
            ArgValue::Seq(v) => {
                write!(out, "[")?;
                for (idx, v) in v.iter().enumerate() {
                    let is_first = idx == 0;
                    if !is_first {
                        write!(out, ", ")?;
                    }
                    serialize_bit_vec(v, out, format)?;
                }
                write!(out, "]")
            }
        }
    }
}

#[inline]
fn serialize_bit_vec(
    value: &Word,
    out: &mut impl Write,
    format: &TraceFormat,
) -> std::io::Result<()> {
    if format.display_hex {
        write!(out, "0x{value:x}")
    } else {
        write!(out, "{value}")
    }
}

impl<O: Write> TraceMonitor<O> {
    pub fn new(protocols: &[Protocol], format: TraceFormat, out: O) -> std::io::Result<Self> {
        let proto_names = protocols.iter().map(|p| p.name.clone()).collect();
        let proto_ignore = if format.include_idle {
            vec![false; protocols.len()]
        } else {
            protocols.iter().map(|p| p.is_idle).collect()
        };
        Ok(Self {
            format,
            out,
            proto_names,
            proto_ignore,
            transactions: vec![],
            max_instances: usize::MAX,
        })
    }

    fn init(
        &mut self,
        st: &SymbolTable,
        protocols: &[Protocol],
        max_instances: usize,
    ) -> std::io::Result<()> {
        debug_assert!(self.transactions.is_empty());
        self.max_instances = max_instances;
        let max_entries = max_instances * protocols.len();
        self.transactions = vec![Transaction::default(); max_entries];
        for (proto_idx, proto) in protocols.iter().enumerate() {
            let args: Vec<_> = proto.args.iter().map(|a| ArgValue::empty(st, a)).collect();
            for slot in 0..max_instances {
                let tran_idx = proto_idx * max_instances + slot;
                self.transactions[tran_idx].args = args.clone();
            }
        }

        if !self.format.status_only {
            writeln!(self.out, "// trace 0")?;
            writeln!(self.out, "trace {{")?;
        }
        Ok(())
    }

    fn start(&mut self, instance: InstanceId, step: u32) {
        let tran_idx = self.transaction_id(instance);
        let tran = &mut self.transactions[tran_idx];
        tran.start = step;
        tran.active = true;
        // println!("[{step}] start {}", self.proto_names[instance.0]);
    }

    fn finish(&mut self, instance: InstanceId, step: u32) -> std::io::Result<()> {
        let tran_idx = self.transaction_id(instance);
        let tran = &mut self.transactions[tran_idx];
        tran.active = false;
        if self.format.status_only || self.proto_ignore[instance.0] {
            return Ok(());
        }
        // println!("[{step}] finish {}", self.proto_names[instance.0]);
        write!(self.out, "    {}(", self.proto_names[instance.0])?;
        for (idx, value) in tran.args.iter().enumerate() {
            let is_first = idx == 0;
            if !is_first {
                write!(self.out, ", ")?;
            }
            value.serialize(&mut self.out, &self.format)?;
        }
        let end = step;
        let start = tran.start;
        if self.format.show_steps {
            if start == end {
                writeln!(self.out, "); [{start}]")?;
            } else {
                writeln!(self.out, "); [{start} .. {end}]")?;
            }
        } else if self.format.show_waveform_time {
            todo!("add support for showing real time");
        } else {
            writeln!(self.out, ");")?;
        }

        for arg in tran.args.iter_mut() {
            arg.clear();
        }

        Ok(())
    }

    fn learn_param(&mut self, instance: InstanceId, arg_idx: usize, value: Word, _step: u32) {
        let tran_idx = self.transaction_id(instance);
        let tran = &mut self.transactions[tran_idx];
        // debug_assert!(tran.active);
        tran.args[arg_idx].learn(value);
        // println!("[{step}] learned {}.{}.{} = 0x{}", self.proto_names[instance.0], instance.1, arg_idx, value.to_hex_str());
    }

    fn transaction_id(&mut self, instance: InstanceId) -> usize {
        debug_assert!(!self.transactions.is_empty(), "init has not been called!");
        instance.0 * self.max_instances + instance.1
    }
}

struct Compiler {
    states: Vec<ExecState>,
    expr: Vec<ExecExpr>,
    regs: Vec<Word>,
    heads: Vec<(usize, usize)>,
    port_symbol_to_index: FxHashMap<SymbolId, usize>,
    reg_symbol_to_index_and_instance: FxHashMap<SymbolId, (usize, InstanceId)>,
    patronus_expr_map: FxHashMap<ExprRef, ExecExprId>,
    simplifier: Simplifier<SparseExprMap<Option<ExprRef>>>,
}

impl Default for Compiler {
    fn default() -> Self {
        Self {
            states: vec![],
            expr: vec![],
            regs: vec![],
            heads: vec![],
            port_symbol_to_index: Default::default(),
            reg_symbol_to_index_and_instance: Default::default(),
            patronus_expr_map: Default::default(),
            simplifier: Simplifier::new(SparseExprMap::default()),
        }
    }
}

impl Compiler {
    fn clear(&mut self) {
        self.states.clear();
        self.expr.clear();
        self.regs.clear();
        self.heads.clear();
        self.port_symbol_to_index.clear();
        self.reg_symbol_to_index_and_instance.clear();
        self.patronus_expr_map.clear();
        self.simplifier = Simplifier::new(SparseExprMap::default());
    }

    fn add_expr(&mut self, expr_ref: ExprRef, expr: ExecExpr) -> ExecExprId {
        let id = self.expr.len().into();
        self.patronus_expr_map.insert(expr_ref, id);
        self.expr.push(expr);
        id
    }
    fn compile(
        &mut self,
        st: &SymbolTable,
        ctx: &mut Context,
        auto: &JointMonitorAutomaton,
        port_map: &PortMap,
    ) {
        self.clear();

        self.heads = auto
            .control
            .bank_counts
            .iter()
            .map(|&count| (0usize, count))
            .collect();

        let num_states = auto.control.graph.nodes().count();
        assert!(
            num_states < u8::MAX as usize,
            "Can only represent up to 256 states!"
        );

        // allocate space for registers
        let mut registers: Vec<_> = auto.registers.iter().map(|(k, v)| (*k, *v)).collect();
        // group by protocol and argument, then sort by slot
        registers.sort_by_key(|((prot, slot, arg), _)| (*prot, *arg, *slot));
        for ((proto_id, slot, _arg_sym), reg) in registers {
            let instance: InstanceId = (proto_id, slot);
            let base_index = self.reg_symbol_to_index_and_instance.len() - slot;
            self.reg_symbol_to_index_and_instance
                .insert(reg, (base_index, instance));
            let expr_ref = auto.control.graph.symbol_expr[&reg];
            self.add_expr(expr_ref, ExecExpr::Reg(base_index, instance));
            let Expr::BVLiteral(init_value) = &ctx[auto.register_inits[&reg]] else {
                panic!("Failed to find init value for {}", st[reg].full_name(st));
            };
            self.regs.push(init_value.get(ctx).to_u64().unwrap());
        }

        // create mappings for dut pins
        for (port, index) in port_map.iter() {
            assert_eq!(port.instance_id, 0);
            let sym = port.pin_id;
            self.port_symbol_to_index.insert(sym, *index);
            let expr_ref = auto.control.graph.symbol_expr[&sym];
            self.add_expr(expr_ref, ExecExpr::DutPin(*index));
        }

        // TODO: make sure that all nodes are reachable
        for (idx, (node_id, _)) in auto.control.graph.nodes().enumerate() {
            assert_eq!(idx, node_id.as_u32() as usize);
            let state =
                self.compile_state(st, ctx, &auto.control.graph, &auto.action_owners, node_id);
            assert_eq!(idx, self.states.len());
            self.states.push(state);
        }
    }

    fn compile_state(
        &mut self,
        st: &SymbolTable,
        ctx: &mut Context,
        pg: &ProtoGraph,
        action_owners: &FxHashMap<(NodeId, usize), InstanceId>,
        node: NodeId,
    ) -> ExecState {
        // compile actions
        let mut acts = vec![];
        for (act_idx, act) in pg[node].actions.iter().enumerate() {
            let is_done = matches!(&pg[act.op], Op::Done);
            if is_done || act.guard == ctx.get_false() {
                continue;
            }
            let Some(instance_owner) = action_owners.get(&(node, act_idx)).cloned() else {
                panic!(
                    "No action owner for {node:?} {act:?} {:?} ({act_idx})",
                    pg[act.op]
                );
            };
            let guard = self.compile_expr(ctx, act.guard);
            match &pg[act.op] {
                Op::Assign(lhs, rhs) => {
                    assert_eq!(act.guard, ctx.get_true());
                    assert_eq!(st[lhs].kind(), AutomatonState);
                    let Some((base_index, instance)) =
                        self.reg_symbol_to_index_and_instance.get(lhs).cloned()
                    else {
                        panic!("{} is not found!", st[lhs].full_name(st))
                    };

                    // we only translate concrete assignments
                    let concrete_full_guards = parallel_assignment_guards(ctx, rhs);
                    assert_eq!(rhs.concretes.len(), concrete_full_guards.len());
                    for ((_, value), guard) in rhs.concretes.iter().zip(concrete_full_guards.iter())
                    {
                        let guard = self.compile_expr(ctx, *guard);
                        let value = self.compile_expr(ctx, *value);
                        let act = ExecAct::AssignReg(base_index, instance, value);
                        acts.push((guard, act));
                    }
                }
                Op::AssertEq(a, b) => {
                    let a = self.compile_expr(ctx, *a);
                    let b = self.compile_expr(ctx, *b);
                    acts.push((guard, ExecAct::AssertEq(a, b)));
                }
                Op::Fork => unreachable!("forks should have been resolved!"),
                Op::InternalAssertFalse => {
                    acts.push((guard, ExecAct::InternalAssertFalse));
                }
                Op::Done => unreachable!("we skip done earlier"),
                &Op::Finish(inst_id) => {
                    assert_eq!(
                        inst_id, instance_owner,
                        "TODO: looks like we have some redundant info here!"
                    );
                    acts.push((guard, ExecAct::Finish(inst_id)));
                }
                &Op::Start(inst_id) => {
                    assert_eq!(
                        inst_id, instance_owner,
                        "TODO: looks like we have some redundant info here!"
                    );
                    acts.push((guard, ExecAct::Start(inst_id)));
                }
                &Op::LearnedParam(arg_id, expr) => {
                    let inst_id = instance_owner;
                    let expr = self.compile_expr(ctx, expr);
                    acts.push((guard, ExecAct::LearnedParam(inst_id, arg_id, expr)));
                }
            }
        }

        // head incr happens on transitions
        for tran in &pg[node].transitions {
            for rot in &tran.rotations {
                if tran.guard != ctx.get_false() {
                    let guard = self.compile_expr(ctx, tran.guard);
                    acts.push((guard, ExecAct::IncrHead(rot.proto_id, rot.amount)));
                }
            }
        }

        // we need actions to happen in the correct order
        // IncrHead < Finish < LearnedParam < Start < ...
        acts.sort_by_key(|(_, a)| match a {
            ExecAct::IncrHead(_, _) => -0,
            ExecAct::Finish(_) => -1,
            ExecAct::LearnedParam(_, _, _) => -2,
            ExecAct::Start(_) => -3,
            ExecAct::InternalAssertFalse
            | ExecAct::AssignReg(_, _, _)
            | ExecAct::AssertEq(_, _) => -10,
        });

        // let transition_guards: Vec<_> = pg[node].transitions.iter().map(|t| format!("{:?}: {}", t.guard, t.guard.serialize_to_str(ctx))).collect();
        // println!("Transition Guards: {}", transition_guards.join(", "));

        let trans: Vec<_> = pg[node]
            .transitions
            .iter()
            .flat_map(|t| {
                assert!(t.consumes_step);
                (t.guard != ctx.get_false()).then(|| {
                    let guard = self.compile_expr(ctx, t.guard);
                    (guard, t.target.as_u32() as u8)
                })
            })
            .collect();

        let mut unique_guards: Vec<_> = acts
            .iter()
            .map(|(guard, _)| *guard)
            .chain(trans.iter().map(|(guard, _)| *guard))
            .collect();
        unique_guards.sort_unstable();
        unique_guards.dedup();

        ExecState {
            acts,
            trans,
            unique_guards,
        }
    }

    fn compile_expr(&mut self, ctx: &mut Context, e: ExprRef) -> ExecExprId {
        let e = self.simplifier.simplify(ctx, e);

        if let Some(expr) = self.patronus_expr_map.get(&e) {
            *expr
        } else {
            let width = e.get_bv_type(ctx).unwrap();
            let mask = (1u64 << width) - 1;
            let expr = match &ctx[e] {
                Expr::BVLiteral(v) => ExecExpr::Lit(v.get(ctx).to_u64().unwrap()),
                Expr::BVSymbol { .. } => unreachable!(
                    "Symbols should be handled earlier: {}",
                    e.serialize_to_str(ctx)
                ),
                &Expr::BVNot(e, _) => {
                    let e = self.compile_expr(ctx, e);
                    ExecExpr::Not(e)
                }
                &Expr::BVOr(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Or, a, b, mask)
                }
                &Expr::BVAnd(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::And, a, b, mask)
                }
                &Expr::BVXor(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Xor, a, b, mask)
                }
                &Expr::BVAdd(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Add, a, b, mask)
                }
                &Expr::BVSub(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Sub, a, b, mask)
                }
                &Expr::BVEqual(a, b) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Equal, a, b, mask)
                }
                &Expr::BVGreaterEqual(a, b) => {
                    let a = self.compile_expr(ctx, a);
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::GreaterEqual, a, b, mask)
                }
                &Expr::BVConcat(a, b, _) => {
                    let a = self.compile_expr(ctx, a);
                    let b_width = b.get_bv_type(ctx).unwrap();
                    let b = self.compile_expr(ctx, b);
                    ExecExpr::Bin(BOp::Concat, a, b, b_width as Word)
                }
                &Expr::BVSlice { e, hi, lo } => {
                    let e = self.compile_expr(ctx, e);
                    ExecExpr::Slice(e, hi, lo)
                }
                &Expr::BVIte { cond, tru, fals } => {
                    let cond = self.compile_expr(ctx, cond);
                    let tru = self.compile_expr(ctx, tru);
                    let fals = self.compile_expr(ctx, fals);
                    ExecExpr::Ite(cond, tru, fals)
                }
                _ => todo!("{}", e.serialize_to_str(ctx)),
            };
            self.add_expr(e, expr)
        }
    }
}

/// returns mutually exclusive guards for each concrete assignment
/// TODO: merge this functionality with the BDD based simplification code
fn parallel_assignment_guards(ctx: &mut Context, assignment: &Assignment) -> Vec<ExprRef> {
    let mut path = ctx.get_true();
    assignment
        .concretes
        .iter()
        .map(|&(cond, _)| {
            let full_cond = and(ctx, path, cond);
            let not_cond = not(ctx, cond);
            path = and(ctx, path, not_cond);
            full_cond
        })
        .collect()
}

/// optimizing or TODO:dedup
#[allow(dead_code)]
fn or(ctx: &mut Context, a: ExprRef, b: ExprRef) -> ExprRef {
    if a == ctx.get_true() || b == ctx.get_true() {
        ctx.get_true()
    } else if b == ctx.get_false() {
        a
    } else if a == ctx.get_false() {
        b
    } else if a == b {
        a
    } else {
        ctx.or(a, b)
    }
}

/// optimizing not TODO:dedup
fn not(ctx: &mut Context, a: ExprRef) -> ExprRef {
    if a == ctx.get_true() {
        ctx.get_false()
    } else if a == ctx.get_false() {
        ctx.get_true()
    } else if let Expr::BVNot(inner, _) = &ctx[a] {
        *inner
    } else {
        ctx.not(a)
    }
}

/// optimizing and TODO: dedup
fn and(ctx: &mut Context, a: ExprRef, b: ExprRef) -> ExprRef {
    if a == ctx.get_false() || b == ctx.get_false() {
        ctx.get_false()
    } else if b == ctx.get_true() {
        a
    } else if a == ctx.get_true() {
        b
    } else if a == b {
        a
    } else {
        ctx.and(a, b)
    }
}

#[derive(Debug)]
struct ExecState {
    unique_guards: Vec<ExecExprId>,
    acts: Vec<(ExecExprId, ExecAct)>,
    trans: Vec<(ExecExprId, u8)>,
}

#[derive(Debug, Clone)]
enum ExecAct {
    InternalAssertFalse,
    AssignReg(usize, InstanceId, ExecExprId),
    AssertEq(ExecExprId, ExecExprId),
    /// indicates that a particular transaction finishes at the end of the cycle
    Finish(InstanceId),
    /// indicates that a particular transaction started at the beginning of the cycle
    Start(InstanceId),
    /// increment the head count for the protocol, (protocol_id, amount)
    IncrHead(ProtocolId, usize),
    /// Indicates that a parameter was learned, (protocol_instance, arg_index, expr)
    LearnedParam(InstanceId, usize, ExecExprId),
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
enum ExecExpr {
    Lit(Word),
    /// look up register value
    Reg(usize, InstanceId),
    /// look up dut pin value
    DutPin(usize),
    // unup
    Not(ExecExprId),
    Slice(ExecExprId, WidthInt, WidthInt),
    // binop
    Bin(BOp, ExecExprId, ExecExprId, Word),
    Ite(ExecExprId, ExecExprId, ExecExprId),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum BOp {
    And,
    Or,
    Xor,
    Equal,
    GreaterEqual,
    Add,
    Sub,
    Concat,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
struct ExecExprId(u32);

impl From<usize> for ExecExprId {
    fn from(value: usize) -> Self {
        Self(value as u32)
    }
}

impl From<ExecExprId> for usize {
    fn from(id: ExecExprId) -> Self {
        id.0 as usize
    }
}
