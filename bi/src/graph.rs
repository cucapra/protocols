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

use baa::{BitVecOps, BitVecValue};
use bi::signal_trace::PortMap;
use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode};
use protocols::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use protocols::ir::graphviz::to_dot_string;
use protocols::ir::joint_monitor::JointMonitorAutomaton;
use protocols::ir::proto_graph::{Assignment, Node, NodeId, Op, ProtoGraph};
use rustc_hash::{FxHashMap, FxHashSet};

pub struct GraphBi {
    pg: ProtoGraph,

    current_state: usize,
    states: Vec<ExecState>,
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

        todo!()
    }
}

impl GraphBi {
    fn exec_state(&mut self, state_id: usize) -> usize {
        let state = &self.states[state_id];
        // first we evaluate all unique guards
        let mut guard_bits = 0u64;
        for guard in &state.guards {
            let value = self.eval(*guard).to_u64().unwrap();
            debug_assert_eq!(value, value & 1);
            guard_bits = guard_bits << 1 | value;
        }

        // eval actions based on guards
        for (act_guard_idx, act) in &state.acts {
            if (guard_bits >> act_guard_idx) & 1 == 1 {
                self.exec_act(act);
            }
        }

        // calc next state based in guards:
        let next_state = state.trans[guard_bits as usize] as usize;
        debug_assert!(next_state < self.states.len());
        next_state
    }

    fn exec_act(&self, act: &ExecAct) {
        todo!()
    }

    fn eval(&self, e: ExecExprId) -> BitVecValue {
        match e {
            _ => todo!(),
        }
    }
}

#[derive(Debug, Default)]
struct Compiler {
    states: Vec<ExecState>,
    expr: Vec<ExecExpr>,
    // TODO: this could be handled by an index map!
    expr_ids: FxHashMap<ExecExpr, ExecExprId>,
    port_symbol_to_index: FxHashMap<SymbolId, usize>,
    reg_symbol_to_index: FxHashMap<SymbolId, usize>,
    patronus_expr_map: FxHashMap<ExprRef, ExecExprId>,
}

impl Compiler {
    fn clear(&mut self) {
        self.states.clear();
        self.expr.clear();
        self.expr_ids.clear();
        self.port_symbol_to_index.clear();
        self.reg_symbol_to_index.clear();
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

        // allocate space for registers
        for &reg in auto.registers.values() {
            let index = self.reg_symbol_to_index.len();
            self.reg_symbol_to_index.insert(reg, index);
            let expr = self.add_expr(ExecExpr::Reg(index));
            self.patronus_expr_map
                .insert(auto.control.graph.symbol_expr[&reg], expr);
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
        let guards = guards
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
                    let (lhs, port_not_reg) = match st[lhs].kind() {
                        SymbolKind::InPort | SymbolKind::OutPort => {
                            let Some(lhs) = self.port_symbol_to_index.get(lhs).cloned() else {
                                panic!("{} is not found!", st[lhs].full_name(st))
                            };
                            (lhs, true)
                        }
                        SymbolKind::AutomatonState => {
                            let Some(lhs) = self.reg_symbol_to_index.get(lhs).cloned() else {
                                panic!("{} is not found!", st[lhs].full_name(st))
                            };
                            (lhs, false)
                        }
                        SymbolKind::Arg(_) => unreachable!("arg is immutable"),
                        SymbolKind::LoopVar => unreachable!("loopvar is immutable"),
                        SymbolKind::Dut => unreachable!("should never encounter dut!"),
                    };

                    // we only translate concrete assignments
                    let concrete_full_guards = parallel_assignment_guards(ctx, rhs);
                    assert_eq!(rhs.concretes.len(), concrete_full_guards.len());
                    for ((_, value), guard) in rhs.concretes.iter().zip(concrete_full_guards.iter())
                    {
                        let guard_id = guard_to_index[guard];
                        let value = self.compile_expr(ctx, &guard_to_index, *value);
                        let act = if port_not_reg {
                            ExecAct::AssignPort(lhs, value)
                        } else {
                            ExecAct::AssignReg(lhs, value)
                        };
                        act_by_guard
                            .entry(guard_id)
                            .or_insert_with(|| vec![])
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
                Op::Fork => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::Fork);
                }
                Op::InternalAssertFalse => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::InternalAssertFalse);
                }
                Op::Done => {
                    act_by_guard
                        .entry(guard_id)
                        .or_insert_with(|| vec![])
                        .push(ExecAct::Done);
                }
            }
        }

        ExecState {
            guards,
            acts: vec![],
            trans: vec![],
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
    // indexed by bits of guard evaluation
    trans: Vec<u16>,
}

#[derive(Debug)]
enum ExecAct {
    Done,
    InternalAssertFalse,
    Fork,
    // target, expr
    AssignPort(usize, ExecExprId),
    AssignReg(usize, ExecExprId),
    AssertEq(ExecExprId, ExecExprId),
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
enum ExecExpr {
    Lit(BitVecValue),
    /// look up local guard expression which must have already been computed
    Guard(usize),
    /// look up register value
    Reg(usize),
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
