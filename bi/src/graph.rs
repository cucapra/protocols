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
use baa::{BitVecMutOps, BitVecOps, BitVecValue};
use bi::signal_trace::{PortMap, SignalValues};
use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode, WidthInt};
use protocols::frontend::ast::Protocol;
use protocols::frontend::symbol::SymbolKind::AutomatonState;
use protocols::frontend::symbol::{Arg, SymbolId, SymbolTable, Type};
use protocols::ir::joint_automaton::ProtocolId;
use protocols::ir::joint_monitor::{InstanceId, JointMonitorAutomaton};
use protocols::ir::proto_graph::{Assignment, Node, NodeId, Op, ProtoGraph};
use rustc_hash::FxHashMap;
use std::io::Write;

pub struct GraphBi<O: Write> {
    // static during execution
    bad_state: usize,
    states: Vec<ExecState>,
    expr: Vec<ExecExpr>,
    // updated during execution
    step: u32,
    current_state: usize,
    regs: Vec<BitVecValue>,
    /// per protocol head counters
    heads: Vec<(usize, usize)>,
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
            expr: c.expr,
            regs: c.regs,
            heads: c.heads,
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
        // first we evaluate all unique guards
        let mut guard_bits = 0u128;
        for (guard_idx, guard) in state.guards.iter().enumerate() {
            let value = self.eval(*guard, guard_bits, &pin_values).to_u64().unwrap() as u128;
            debug_assert_eq!(value, value & 1);
            guard_bits |= value << guard_idx;
        }

        // eval actions based on guards
        for (act_guard_idx, act) in &state.acts {
            if (guard_bits >> act_guard_idx) & 1 == 1 {
                match act.clone() {
                    ExecAct::InternalAssertFalse => {
                        panic!("Internal assertion failed! State {}", self.current_state)
                    }
                    ExecAct::AssignReg(idx, instance, value) => {
                        let value = self.eval(value, guard_bits, &pin_values);
                        let idx = self.reg_idx(idx, instance);
                        self.regs[idx] = value;
                    }
                    ExecAct::AssertEq(lhs, rhs) => {
                        let lhs = self.eval(lhs, guard_bits, &pin_values);
                        let rhs = self.eval(rhs, guard_bits, &pin_values);
                        let is_ok = lhs.is_equal(&rhs);
                        if !is_ok {
                            panic!("assertion failed");
                        }
                    }
                    ExecAct::Finish(instance) => {
                        let instance = self.eval_instance_id(instance);
                        self.mon.finish(instance, self.step)?;
                    }
                    ExecAct::Start(instance) => {
                        let instance = self.eval_instance_id(instance);
                        self.mon.start(instance, self.step);
                    }
                    ExecAct::IncrHead(proto_id, amount) => {
                        let (old, count) = self.heads[proto_id];
                        self.heads[proto_id].0 = (old + amount) % count;
                    }
                    ExecAct::LearnedParam(instance, arg_idx, expr) => {
                        let value = self.eval(expr, guard_bits, &pin_values);
                        let instance = self.eval_instance_id(instance);
                        self.mon.learn_param(instance, arg_idx, value, self.step);
                    }
                }
            }
        }

        // calc next state based in guards:
        let next = state
            .trans
            .iter()
            .find(|(g, _)| (guard_bits >> g) & 1 == 1)
            .cloned()
            .unwrap()
            .1 as usize;
        Ok(next)
    }

    #[inline]
    fn eval_instance_id(&self, id: InstanceId) -> InstanceId {
        let (proto_id, base_instance) = id;
        let (head, count) = self.heads[proto_id];
        let instance = (base_instance + head) % count;
        (proto_id, instance)
    }

    fn eval(&self, e: ExecExprId, guard_bits: u128, pin_values: &SignalValues) -> BitVecValue {
        match self.expr[e.0].clone() {
            ExecExpr::Lit(v) => v,
            ExecExpr::Guard(idx) => BitVecValue::from_bool((guard_bits >> idx) & 1 == 1),
            ExecExpr::Reg(idx, instance) => self.regs[self.reg_idx(idx, instance)].clone(),
            ExecExpr::DutPin(idx) => pin_values[idx].clone(),
            ExecExpr::Not(e) => self.eval(e, guard_bits, pin_values).not(),
            ExecExpr::Slice(e, hi, lo) => self.eval(e, guard_bits, pin_values).slice(hi, lo),
            ExecExpr::Bin(op, a, b) => {
                let a = self.eval(a, guard_bits, pin_values);
                let b = self.eval(b, guard_bits, pin_values);
                match op {
                    BOp::And => a.and(&b),
                    BOp::Or => a.or(&b),
                    BOp::Equal => a.is_equal(&b).into(),
                    BOp::GreaterEqual => a.is_greater_or_equal(&b).into(),
                    BOp::Add => a.add(&b),
                    BOp::Sub => a.sub(&b),
                    BOp::Concat => a.concat(&b),
                }
            }
            ExecExpr::Ite(cond, tru, fals) => {
                let cond = self.eval(cond, guard_bits, pin_values);
                if cond.is_true() {
                    self.eval(tru, guard_bits, pin_values)
                } else {
                    self.eval(fals, guard_bits, pin_values)
                }
            }
        }
    }

    #[inline]
    fn reg_idx(&self, idx: usize, instance: InstanceId) -> usize {
        let instance = self.eval_instance_id(instance);
        idx + instance.1
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
    Scalar(BitVecValue),
    Seq(Vec<BitVecValue>),
}

impl ArgValue {
    fn empty(st: &SymbolTable, arg: &Arg) -> Self {
        match st[arg.symbol()].tpe() {
            Type::UnsignedInt => Self::Scalar(BitVecValue::zero(64)),
            Type::BitVec(w) => Self::Scalar(BitVecValue::zero(w)),
            Type::Seq(_) => Self::Seq(vec![]),
            Type::Tuple(_) => todo!("tuple"),
            Type::Struct(_) | Type::Unknown => unreachable!(),
        }
    }

    #[inline]
    fn clear(&mut self) {
        match self {
            ArgValue::Scalar(s) => s.clear(),
            ArgValue::Seq(s) => s.clear(),
        }
    }

    #[inline]
    fn learn(&mut self, value: BitVecValue) {
        match self {
            ArgValue::Scalar(s) => s.assign(&value),
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
    value: &BitVecValue,
    out: &mut impl Write,
    format: &TraceFormat,
) -> std::io::Result<()> {
    if format.display_hex {
        write!(out, "0x{}", value.to_hex_str())
    } else {
        write!(out, "{}", value.to_dec_str())
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

    fn learn_param(
        &mut self,
        instance: InstanceId,
        arg_idx: usize,
        value: BitVecValue,
        _step: u32,
    ) {
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

#[derive(Debug, Default)]
struct Compiler {
    states: Vec<ExecState>,
    expr: Vec<ExecExpr>,
    regs: Vec<BitVecValue>,
    heads: Vec<(usize, usize)>,
    // TODO: this could be handled by an index map!
    expr_ids: FxHashMap<ExecExpr, ExecExprId>,
    port_symbol_to_index: FxHashMap<SymbolId, usize>,
    reg_symbol_to_index_and_instance: FxHashMap<SymbolId, (usize, InstanceId)>,
    patronus_expr_map: FxHashMap<ExprRef, ExecExprId>,
}

impl Compiler {
    fn clear(&mut self) {
        self.states.clear();
        self.expr.clear();
        self.regs.clear();
        self.heads.clear();
        self.expr_ids.clear();
        self.port_symbol_to_index.clear();
        self.reg_symbol_to_index_and_instance.clear();
        self.patronus_expr_map.clear();
    }

    fn add_expr(&mut self, expr: ExecExpr) -> ExecExprId {
        if let Some(id) = self.expr_ids.get(&expr) {
            *id
        } else {
            let id = self.expr.len().into();
            self.expr_ids.insert(expr.clone(), id);
            self.expr.push(expr);
            id
        }
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
            let expr = self.add_expr(ExecExpr::Reg(base_index, instance));
            self.patronus_expr_map
                .insert(auto.control.graph.symbol_expr[&reg], expr);
            let Expr::BVLiteral(init_value) = &ctx[auto.register_inits[&reg]] else {
                panic!("Failed to find init value for {}", st[reg].full_name(st));
            };
            self.regs.push(init_value.get(ctx).into());
        }

        // create mappings for dut pins
        for (port, index) in port_map.iter() {
            assert_eq!(port.instance_id, 0);
            let sym = port.pin_id;
            self.port_symbol_to_index.insert(sym, *index);
            let expr = self.add_expr(ExecExpr::DutPin(*index));
            self.patronus_expr_map
                .insert(auto.control.graph.symbol_expr[&sym], expr);
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
        // first we collect all guards and dedup them
        let mut guards: Vec<_> = all_guards(ctx, pg, &pg[node]);
        // add a static "true" guard to the front
        guards.insert(0, ctx.get_true());

        // compile guards
        let mut guard_to_index = FxHashMap::default();
        let guards: Vec<_> = guards
            .into_iter()
            .enumerate()
            .map(|(idx, g)| {
                let compiled = self.compile_expr(ctx, &guard_to_index, g);
                guard_to_index.insert(g, idx);
                compiled
            })
            .collect();

        // group actions by guards
        let mut act_by_guard = FxHashMap::<usize, Vec<ExecAct>>::default();
        for (act_idx, act) in pg[node].actions.iter().enumerate() {
            let is_done = matches!(&pg[act.op], Op::Done);
            if is_done {
                continue;
            }
            let Some(instance_owner) = action_owners.get(&(node, act_idx)).cloned() else {
                panic!(
                    "No action owner for {node:?} {act:?} {:?} ({act_idx})",
                    pg[act.op]
                );
            };
            let guard_id = guard_to_index[&act.guard];
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
                        let guard_id = guard_to_index[guard];
                        let value = self.compile_expr(ctx, &guard_to_index, *value);
                        let act = ExecAct::AssignReg(base_index, instance, value);
                        act_by_guard
                            .entry(guard_id)
                            .or_insert_with(Vec::new)
                            .push(act);
                    }
                }
                Op::AssertEq(a, b) => {
                    let a = self.compile_expr(ctx, &guard_to_index, *a);
                    let b = self.compile_expr(ctx, &guard_to_index, *b);
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::AssertEq(a, b));
                }
                Op::Fork => unreachable!("forks should have been resolved!"),
                Op::InternalAssertFalse => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::InternalAssertFalse);
                }
                Op::Done => unreachable!("we skip done earlier"),
                &Op::Finish(inst_id) => {
                    assert_eq!(
                        inst_id, instance_owner,
                        "TODO: looks like we have some redundant info here!"
                    );
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(Vec::new)
                        .push(ExecAct::Finish(inst_id));
                }
                &Op::Start(inst_id) => {
                    assert_eq!(
                        inst_id, instance_owner,
                        "TODO: looks like we have some redundant info here!"
                    );
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(Vec::new)
                        .push(ExecAct::Start(inst_id));
                }
                &Op::LearnedParam(arg_id, expr) => {
                    let inst_id = instance_owner;
                    let expr = self.compile_expr(ctx, &guard_to_index, expr);
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(Vec::new)
                        .push(ExecAct::LearnedParam(inst_id, arg_id, expr));
                }
            }
        }

        let mut acts: Vec<_> = act_by_guard
            .iter()
            .flat_map(|(g, acts)| acts.iter().map(|a| (*g, a.clone())))
            .collect();
        // head incr happens on transitions
        for tran in &pg[node].transitions {
            for rot in &tran.rotations {
                if tran.guard != ctx.get_false() {
                    let guard_id = guard_to_index[&tran.guard];
                    acts.push((guard_id, ExecAct::IncrHead(rot.proto_id, rot.amount)));
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

        let trans = pg[node]
            .transitions
            .iter()
            .filter(|t| t.guard != ctx.get_false())
            .map(|t| {
                assert!(t.consumes_step);
                (guard_to_index[&t.guard], t.target.as_u32() as u8)
            })
            .collect();

        ExecState {
            guards,
            acts,
            trans,
        }
    }

    fn compile_expr(
        &mut self,
        ctx: &Context,
        guard_to_index: &FxHashMap<ExprRef, usize>,
        e: ExprRef,
    ) -> ExecExprId {
        if let Some(guard_idx) = guard_to_index.get(&e) {
            self.add_expr(ExecExpr::Guard(*guard_idx))
        } else if let Some(expr) = self.patronus_expr_map.get(&e) {
            *expr
        } else {
            let expr = match &ctx[e] {
                Expr::BVLiteral(v) => ExecExpr::Lit(v.get(ctx).into()),
                Expr::BVSymbol { .. } => unreachable!(
                    "Symbols should be handled earlier: {}",
                    e.serialize_to_str(ctx)
                ),
                &Expr::BVNot(e, _) => {
                    let e = self.compile_expr(ctx, guard_to_index, e);
                    ExecExpr::Not(e)
                }
                &Expr::BVOr(a, b, _) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::Or, a, b)
                }
                &Expr::BVAnd(a, b, _) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::And, a, b)
                }
                &Expr::BVAdd(a, b, _) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::Add, a, b)
                }
                &Expr::BVSub(a, b, _) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::Sub, a, b)
                }
                &Expr::BVEqual(a, b) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::Equal, a, b)
                }
                &Expr::BVGreaterEqual(a, b) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::GreaterEqual, a, b)
                }
                &Expr::BVConcat(a, b, _) => {
                    let a = self.compile_expr(ctx, guard_to_index, a);
                    let b = self.compile_expr(ctx, guard_to_index, b);
                    ExecExpr::Bin(BOp::Concat, a, b)
                }
                &Expr::BVSlice { e, hi, lo } => {
                    let e = self.compile_expr(ctx, guard_to_index, e);
                    ExecExpr::Slice(e, hi, lo)
                }
                &Expr::BVIte { cond, tru, fals } => {
                    let cond = self.compile_expr(ctx, guard_to_index, cond);
                    let tru = self.compile_expr(ctx, guard_to_index, tru);
                    let fals = self.compile_expr(ctx, guard_to_index, fals);
                    ExecExpr::Ite(cond, tru, fals)
                }
                _ => todo!("{}", e.serialize_to_str(ctx)),
            };
            self.add_expr(expr)
        }
    }
}

fn all_guards(ctx: &mut Context, pg: &ProtoGraph, node: &Node) -> Vec<ExprRef> {
    let mut all: Vec<_> = node
        .actions
        .iter()
        .flat_map(|a| match &pg[a.op] {
            Op::Assign(_, a) => parallel_assignment_guards(ctx, a),
            _ => vec![],
        })
        .chain(node.transitions.iter().map(|t| t.guard))
        .chain(node.actions.iter().map(|a| a.guard))
        .collect();
    all.sort_unstable();
    all.dedup();
    all.retain(|g| *g != ctx.get_true() && *g != ctx.get_false());
    all
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
    guards: Vec<ExecExprId>,
    acts: Vec<(usize, ExecAct)>,
    trans: Vec<(usize, u8)>,
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
    Lit(BitVecValue),
    /// look up local guard expression which must have already been computed
    Guard(usize),
    /// look up register value
    Reg(usize, InstanceId),
    /// look up dut pin value
    DutPin(usize),
    // unup
    Not(ExecExprId),
    Slice(ExecExprId, WidthInt, WidthInt),
    // binop
    Bin(BOp, ExecExprId, ExecExprId),
    Ite(ExecExprId, ExecExprId, ExecExprId),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum BOp {
    And,
    Or,
    Equal,
    GreaterEqual,
    Add,
    Sub,
    Concat,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct ExecExprId(usize);

impl From<usize> for ExecExprId {
    fn from(value: usize) -> Self {
        Self(value)
    }
}
