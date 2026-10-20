use std::collections::VecDeque;

use baa::{BitVecOps, BitVecValue};
use patronus::expr::{Context, Expr, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

use crate::frontend::symbol::SymbolId;
use crate::ir::driver_to_monitor::MonitorAutomaton;
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph};

// TODO: This dataflow analysis is very similar to what we do for
// TODO: reaching definitions, forks, etc. It is slightly more complicated
// TODO: because we need to solve within expressions, but this makes it
// TODO: the most general version that maybe we can extrapolate a general
// TODO: pass for.

/// Disjoint (by invariant) masks of bits definitely zero and definitely one.
/// If a bit is not high in either, we don't know.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KnownBits {
    pub zero: BitVecValue,
    pub one: BitVecValue,
}

impl KnownBits {
    pub fn unknown(width: u32) -> Self {
        Self {
            zero: BitVecValue::zero(width),
            one: BitVecValue::zero(width),
        }
    }

    fn exact(value: BitVecValue) -> Self {
        Self {
            zero: value.not(),
            one: value,
        }
    }

    /// Returns the value when every bit is statically determined.
    pub fn constant(&self) -> Option<BitVecValue> {
        self.zero
            .or(&self.one)
            .is_all_ones()
            .then(|| self.one.clone())
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            zero: self.zero.and(&other.zero),
            one: self.one.and(&other.one),
        }
    }

    pub fn select(condition: &Self, tru: Self, fals: Self) -> Self {
        match condition.constant().and_then(|c| c.to_bool()) {
            Some(true) => tru,
            Some(false) => fals,
            None => tru.join(&fals),
        }
    }
}

pub struct KnownBitsEvaluator<'a> {
    ctx: &'a Context,
    facts: FxHashMap<ExprRef, KnownBits>,
    cache: FxHashMap<ExprRef, KnownBits>,
}

impl<'a> KnownBitsEvaluator<'a> {
    pub fn new(ctx: &'a Context, facts: FxHashMap<ExprRef, KnownBits>) -> Self {
        Self {
            ctx,
            facts,
            cache: FxHashMap::default(),
        }
    }

    /// use a condition known to be true and discard cached results that may
    /// change under this assumption.
    pub fn assume_true(&mut self, condition: ExprRef) {
        assume_true(self.ctx, condition, &mut self.facts);
        self.cache.clear();
    }

    pub fn eval(&mut self, expr: ExprRef) -> KnownBits {
        if let Some(value) = self.facts.get(&expr).or_else(|| self.cache.get(&expr)) {
            return value.clone();
        }
        let width = expr.get_bv_type(self.ctx).unwrap();
        let value = match self.ctx[expr].clone() {
            Expr::BVLiteral(v) => KnownBits::exact(v.get(self.ctx).into()),
            Expr::BVNot(e, _) => {
                let e = self.eval(e);
                KnownBits {
                    zero: e.one,
                    one: e.zero,
                }
            }
            Expr::BVAnd(a, b, _) => {
                let (a, b) = (self.eval(a), self.eval(b));
                KnownBits {
                    zero: a.zero.or(&b.zero),
                    one: a.one.and(&b.one),
                }
            }
            Expr::BVOr(a, b, _) => {
                let (a, b) = (self.eval(a), self.eval(b));
                KnownBits {
                    zero: a.zero.and(&b.zero),
                    one: a.one.or(&b.one),
                }
            }
            Expr::BVXor(a, b, _) => {
                let (a, b) = (self.eval(a), self.eval(b));
                KnownBits {
                    zero: a.zero.and(&b.zero).or(&a.one.and(&b.one)),
                    one: a.zero.and(&b.one).or(&a.one.and(&b.zero)),
                }
            }
            Expr::BVSlice { e, hi, lo } => {
                let e = self.eval(e);
                KnownBits {
                    zero: e.zero.slice(hi, lo),
                    one: e.one.slice(hi, lo),
                }
            }
            Expr::BVConcat(a, b, _) => {
                let (a, b) = (self.eval(a), self.eval(b));
                KnownBits {
                    zero: a.zero.concat(&b.zero),
                    one: a.one.concat(&b.one),
                }
            }
            Expr::BVZeroExt { e, by, .. } => {
                let e = self.eval(e);
                KnownBits {
                    zero: e.zero.not().zero_extend(by).not(),
                    one: e.one.zero_extend(by),
                }
            }
            Expr::BVSignExt { e, by, .. } => {
                let e = self.eval(e);
                KnownBits {
                    zero: e.zero.sign_extend(by),
                    one: e.one.sign_extend(by),
                }
            }
            Expr::BVIte { cond, tru, fals } => {
                KnownBits::select(&self.eval(cond), self.eval(tru), self.eval(fals))
            }
            Expr::BVEqual(a, b) => {
                let (av, bv) = (self.eval(a), self.eval(b));
                if a == b {
                    KnownBits::exact(BitVecValue::new_true())
                } else if !av.zero.and(&bv.one).or(&av.one.and(&bv.zero)).is_zero() {
                    KnownBits::exact(BitVecValue::new_false())
                } else if let (Some(a), Some(b)) = (av.constant(), bv.constant()) {
                    KnownBits::exact(BitVecValue::from_u64(u64::from(a == b), 1))
                } else {
                    KnownBits::unknown(1)
                }
            }
            Expr::BVShiftLeft(a, b, _)
            | Expr::BVShiftRight(a, b, _)
            | Expr::BVArithmeticShiftRight(a, b, _) => {
                let a = self.eval(a);
                match self.eval(b).constant() {
                    None => KnownBits::unknown(width),
                    Some(shift) => {
                        let shift_value = |v: BitVecValue| match self.ctx[expr] {
                            Expr::BVShiftLeft(..) => v.shift_left(&shift),
                            Expr::BVShiftRight(..) => v.shift_right(&shift),
                            _ => v.arithmetic_shift_right(&shift),
                        };
                        KnownBits {
                            zero: shift_value(a.zero.not()).not(),
                            one: shift_value(a.one),
                        }
                    }
                }
            }
            // symbols without supplied facts and/or unsupported operators are unknown.
            _ => KnownBits::unknown(width),
        };
        self.cache.insert(expr, value.clone());
        value
    }
}

fn assume_true(ctx: &Context, expr: ExprRef, facts: &mut FxHashMap<ExprRef, KnownBits>) {
    fn assume(
        ctx: &Context,
        expr: ExprRef,
        value: bool,
        facts: &mut FxHashMap<ExprRef, KnownBits>,
    ) {
        facts.insert(
            expr,
            KnownBits::exact(BitVecValue::from_u64(u64::from(value), 1)),
        );
        match ctx[expr] {
            Expr::BVNot(e, 1) => assume(ctx, e, !value, facts),
            Expr::BVAnd(a, b, 1) if value => {
                assume(ctx, a, true, facts);
                assume(ctx, b, true, facts);
            }
            Expr::BVOr(a, b, 1) if !value => {
                assume(ctx, a, false, facts);
                assume(ctx, b, false, facts);
            }
            _ => {}
        }
    }
    assume(ctx, expr, true, facts);
}

// TODO: This implementation should be the basis for *universal* knownness analysis and register simplification pass

pub type KnownnessFacts = FxHashMap<SymbolId, KnownBits>;

/// Compute node-entry facts, keyed by physical knownness register, to a fixed point.
/// TODO: This function's shape is very much like the other dataflow analyses we have,
/// TODO: so we need to factor this code out to a standard API if possible at some point.
pub fn analyze_knownness(
    ctx: &Context,
    monitor: &MonitorAutomaton,
) -> FxHashMap<NodeId, KnownnessFacts> {
    let graph = &monitor.graph;
    let initial: KnownnessFacts = monitor
        .knownness_registers
        .values()
        .map(|&register| {
            let init = monitor.register_inits[&register];
            let value = KnownBitsEvaluator::new(ctx, FxHashMap::default()).eval(init);
            (register, value)
        })
        .collect();
    // None means no incoming execution has been propagated yet.
    let mut node_entry = graph
        .nodes()
        .map(|(id, _)| (id, None))
        .collect::<FxHashMap<_, _>>();
    node_entry.insert(graph.entry, Some(initial));
    let mut pending = VecDeque::from([graph.entry]);
    while let Some(node) = pending.pop_front() {
        let entry = node_entry[&node].as_ref().unwrap().clone();
        for edge in &graph[node].transitions {
            let expr_facts = expression_facts(graph, &entry);
            let mut eval = KnownBitsEvaluator::new(ctx, expr_facts);
            if eval
                .eval(edge.guard)
                .constant()
                .is_some_and(|c| c.is_false())
            {
                continue;
            }
            // Taking this edge means its condition is true in this cycle.
            // Use that fact when deciding which parameter bits get learned.
            eval.assume_true(edge.guard);
            let out = transfer(graph, node, &entry, &mut eval);
            let target = node_entry.get_mut(&edge.target).unwrap();

            // the join function (0 all bits that don't agree)
            let joined = match target.as_ref() {
                None => out,
                Some(previous) => previous
                    .iter()
                    .map(|(&register, bits)| (register, bits.join(&out[&register])))
                    .collect(),
            };
            if target.as_ref() != Some(&joined) {
                *target = Some(joined);
                pending.push_back(edge.target);
            }
        }
    }
    node_entry
        .into_iter()
        .map(|(node, facts)| {
            let facts = facts.unwrap_or_else(|| {
                panic!("unreachable monitor node {node}: prune unreachable nodes before knownness analysis")
            });
            (node, facts)
        })
        .collect()
}

fn expression_facts(graph: &ProtoGraph, facts: &KnownnessFacts) -> FxHashMap<ExprRef, KnownBits> {
    facts
        .iter()
        .map(|(&register, bits)| (graph.symbol_expr(register).unwrap(), bits.clone()))
        .collect()
}

// update the Knownness facts based on the `Assign` actions to the Knownness registers
// in this current node `node`.
fn transfer(
    graph: &ProtoGraph,
    node: NodeId,
    entry: &KnownnessFacts,
    eval: &mut KnownBitsEvaluator<'_>,
) -> KnownnessFacts {
    let mut out = entry.clone();

    for action in &graph[node].actions {
        // analyze assignments to a register, and check that the register is a knownness register
        // (otherwise, we continue to the next action)
        let Op::Assign(register, assignment) = &graph[action.op] else {
            continue;
        };
        let Some(held) = entry.get(register) else {
            continue;
        };

        let mut value = held.clone();
        // Nest in reverse order so the first applicable alternative wins.
        for &(guard, rhs) in assignment.concretes.iter().rev() {
            value = KnownBits::select(&eval.eval(guard), eval.eval(rhs), value);
        }
        let unknown = KnownBits::unknown(held.zero.width());
        value = KnownBits::select(&eval.eval(assignment.dont_care), unknown, value);
        out.insert(
            *register,
            KnownBits::select(&eval.eval(action.guard), value, held.clone()),
        );
    }
    out
}
