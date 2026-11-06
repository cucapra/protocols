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
use protocols::ir::proto_graph::{Node, NodeId, Op, ProtoGraph};
use rustc_hash::{FxHashMap, FxHashSet};

pub struct GraphBi {
    pg: ProtoGraph,

    current_state: usize,
    states: Vec<ExecState>,
}

impl GraphBi {
    pub fn new(
        st: &SymbolTable,
        ctx: &Context,
        port_map: &PortMap,
        monitor: JointMonitorAutomaton,
    ) -> Self {
        println!("{}", monitor.to_dot_string(ctx, st));

        let mut c = Compiler::default();
        c.compile(st, ctx, &monitor);

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
}

impl Compiler {
    fn compile(&mut self, st: &SymbolTable, ctx: &Context, auto: &JointMonitorAutomaton) {
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
        ctx: &Context,
        pg: &ProtoGraph,
        node: NodeId,
    ) -> ExecState {
        // first we collect all guards and dedup them
        let mut guards: Vec<_> = all_guards(ctx, pg, &pg[node]).collect();
        guards.sort_unstable();
        guards.dedup();
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
                    let lhs = match st[lhs].kind() {
                        SymbolKind::Dut => unreachable!("should never encounter dut!"),
                        SymbolKind::InPort | SymbolKind::OutPort => {
                            let Some(lhs) = self.port_symbol_to_index.get(lhs).cloned() else {
                                panic!("{} is not found!", st[lhs].full_name(st))
                            };
                            lhs
                        }
                        SymbolKind::Arg(_) => unreachable!("arg is immutable"),
                        SymbolKind::LoopVar => unreachable!("loopvar is immutable"),
                        SymbolKind::AutomatonState => todo!("automaton var"),
                    };

                    // we only translate concrete assignments
                    for (guard, value) in &rhs.concretes {
                        let guard_id = guard_to_index[guard];
                        let value = self.compile_expr(ctx, &guard_to_index, *value);
                        let act = ExecAct::Assign(lhs, value);
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
        let expr = if let Some(guard_idx) = guard_to_index.get(&e) {
            ExecExpr::Guard(*guard_idx)
        } else {
            match &ctx[e] {
                Expr::BVLiteral(v) => ExecExpr::Lit(v.get(ctx).into()),
                _ => todo!("{}", e.serialize_to_str(ctx)),
            }
        };
        if let Some(id) = self.expr_ids.get(&expr) {
            *id
        } else {
            let id = self.expr.len().into();
            self.expr_ids.insert(expr.clone(), id);
            self.expr.push(expr);
            id
        }
    }
}

fn all_guards(ctx: &Context, pg: &ProtoGraph, node: &Node) -> impl Iterator<Item = ExprRef> {
    node.actions
        .iter()
        .flat_map(|a| match &pg[a.op] {
            Op::Assign(_, a) => [a.dont_care]
                .into_iter()
                .chain(a.concretes.iter().map(|(g, _)| *g))
                .collect(),
            _ => vec![],
        })
        .chain(node.transitions.iter().map(|t| t.guard))
        .chain(node.actions.iter().map(|a| a.guard))
        .filter(|g| *g != ctx.get_false() && *g != ctx.get_true())
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
    Assign(usize, ExecExprId),
    AssertEq(ExecExprId, ExecExprId),
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
enum ExecExpr {
    Lit(BitVecValue),
    /// look up local guard expression which must have already been computed
    Guard(usize),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct ExecExprId(usize);

impl From<usize> for ExecExprId {
    fn from(value: usize) -> Self {
        Self(value)
    }
}
