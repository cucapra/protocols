// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Graph-IR based reconstructor implementation.

// - build custom runner, we might want to generate results on the fly
// - we do not need to deal with the possibility of multiple traces
// - only support wellen inputs first, can add ascii wave support later
// - group transitions and actions by guard
// - can we save the guard evaluation history in order to decide which one to evaluate first?
// - is there maybe even a way to evaluate guards in parallel?
// - different than the existing bi, we should be able to never allocate during execution
// - we could define an array that contains all relevant values from the trace
//   and then compile expressions to byte code that contains the concrete indices

use crate::bi::Failures;
use baa::{BitVecOps, BitVecValue};
use bi::signal_trace::{PortMap, SignalValues};
use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode};
use protocols::frontend::symbol::SymbolKind::AutomatonState;
use protocols::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use protocols::ir::joint_automaton::ProtocolId;
use protocols::ir::joint_monitor::{InstanceId, JointMonitorAutomaton};
use protocols::ir::proto_graph::{Assignment, Node, NodeId, Op, ProtoGraph};
use rustc_hash::FxHashMap;

pub struct GraphBi {
    // static during execution
    bad_state: usize,
    states: Vec<ExecState>,
    expr: Vec<ExecExpr>,
    // updated during execution
    current_state: usize,
    regs: Vec<BitVecValue>,
    /// per protocol head counters
    heads: Vec<(usize, usize)>,
}

impl GraphBi {
    pub fn new(
        st: &SymbolTable,
        ctx: &mut Context,
        port_map: &PortMap,
        monitor: JointMonitorAutomaton,
    ) -> Self {
        println!("{}", monitor.to_dot_string(ctx, st));
        let mut c = Compiler::default();
        c.compile(st, ctx, &monitor, port_map);

        Self {
            current_state: monitor.control.graph.entry.as_u32() as usize,
            states: c.states,
            expr: c.expr,
            regs: c.regs,
            heads: c.heads,
            bad_state: monitor.bad_state.as_u32() as usize,
        }
    }

    pub fn has_failed(&self) -> bool {
        self.current_state == self.bad_state
    }

    pub fn exec_step(&mut self, values: SignalValues) -> std::result::Result<(), Failures> {
        if self.current_state != self.bad_state {
            print!("{} --> ", self.current_state);
            self.current_state = self.exec_state(self.current_state, values);
            println!("{}", self.current_state);
        }
        Ok(())
    }
}

impl GraphBi {
    fn exec_state(&mut self, state_id: usize, pin_values: SignalValues) -> usize {
        let state = &self.states[state_id];
        // first we evaluate all unique guards
        let mut guard_bits = 0u64;
        for (guard_idx, guard) in state.guards.iter().enumerate() {
            let value = self.eval(*guard, guard_bits, &pin_values).to_u64().unwrap();
            debug_assert_eq!(value, value & 1);
            guard_bits |= value << guard_idx;
        }

        // eval actions based on guards
        for (act_guard_idx, act) in &state.acts {
            if (guard_bits >> act_guard_idx) & 1 == 1 {
                match act {
                    ExecAct::InternalAssertFalse => {
                        panic!("Internal assertion failed! State {}", self.current_state)
                    }
                    &ExecAct::AssignReg(idx, instance, value) => {
                        let value = self.eval(value, guard_bits, &pin_values);
                        let idx = self.reg_idx(idx, instance);
                        self.regs[idx] = value;
                    }
                    ExecAct::AssertEq(lhs, rhs) => {
                        let lhs = self.eval(*lhs, guard_bits, &pin_values);
                        let rhs = self.eval(*rhs, guard_bits, &pin_values);
                        let is_ok = lhs.is_equal(&rhs);
                        if !is_ok {
                            panic!("assertion failed");
                        }
                    }
                    &ExecAct::Finish(instance) => {
                        let instance = self.eval_instance_id(instance);
                        println!(
                            "TODO: protocol {}, instance {} finished!",
                            instance.0, instance.1
                        );
                    }
                    &ExecAct::Start(instance) => {
                        let instance = self.eval_instance_id(instance);
                        println!(
                            "TODO: protocol {}, instance {} started!",
                            instance.0, instance.1
                        );
                    }
                    &ExecAct::IncrHead(proto_id, amount) => {
                        let (old, count) = self.heads[proto_id];
                        self.heads[proto_id].0 = (old + amount) % count;
                    }
                }
            }
        }

        // calc next state based in guards:
        state
            .trans
            .iter()
            .find(|(g, _)| (guard_bits >> g) & 1 == 1)
            .cloned()
            .unwrap()
            .1 as usize
    }

    #[inline]
    fn eval_instance_id(&self, id: InstanceId) -> InstanceId {
        let (proto_id, base_instance) = id;
        let (head, count) = self.heads[proto_id];
        let instance = (base_instance + head) % count;
        (proto_id, instance)
    }

    fn eval(&self, e: ExecExprId, guard_bits: u64, pin_values: &SignalValues) -> BitVecValue {
        match self.expr[e.0].clone() {
            ExecExpr::Lit(v) => v,
            ExecExpr::Guard(idx) => BitVecValue::from_bool((guard_bits >> idx) & 1 == 1),
            ExecExpr::Reg(idx, instance) => self.regs[self.reg_idx(idx, instance)].clone(),
            ExecExpr::DutPin(idx) => pin_values[idx].clone(),
        }
    }

    #[inline]
    fn reg_idx(&self, idx: usize, instance: InstanceId) -> usize {
        let instance = self.eval_instance_id(instance);
        idx + instance.0
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
        for ((proto_id, slot, arg_sym), reg) in registers {
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
            let state = self.compile_state(st, ctx, &auto.control.graph, node_id);
            assert_eq!(idx, self.states.len());
            self.states.push(state);
        }
    }

    fn compile_state(
        &mut self,
        st: &SymbolTable,
        ctx: &mut Context,
        pg: &ProtoGraph,
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
        for act in &pg[node].actions {
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
                Op::Done => {} // TODO: is it ok to ignore done?
                Op::Finish(inst_id) => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::Finish(inst_id.clone()));
                }
                Op::Start(inst_id) => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::Start(inst_id.clone()));
                }
                Op::LearnedParam(..) => todo!("learned param"),
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
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct ExecExprId(usize);

impl From<usize> for ExecExprId {
    fn from(value: usize) -> Self {
        Self(value)
    }
}
