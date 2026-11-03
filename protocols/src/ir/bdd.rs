// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! BDD-based simplification for patronus expressions

use crate::ir::proto_graph::{Assignment, Node, NodeId};
use boolean_expression::Expr as BExpr;
use patronus::expr::{Context, Expr, ExprRef};
use patronus::smt::{CheckSatResponse, SmtLibSolverCtx, SolverContext};
use rustc_hash::FxHashMap;

pub struct NestedIte<V: Clone + PartialEq> {
    dont_care: Option<ExprRef>,
    serial: Vec<(ExprRef, V)>,
}

impl From<&Assignment> for NestedIte<ExprRef> {
    fn from(value: &Assignment) -> Self {
        let dont_care = Some(value.dont_care);
        let values = value.concretes.clone();
        Self {
            dont_care,
            serial: values,
        }
    }
}

impl<V: Clone + PartialEq> NestedIte<V> {
    fn from(ctx: &mut Context, value: ValueSummary<V>) -> Self {
        // in a value summary, all guards are mutually exclusive, so it does not matter in which order they get evaluated
        Self {
            dont_care: value.dont_care,
            serial: value.parallel,
        }
    }

    fn all_guards(&self) -> impl Iterator<Item = ExprRef> {
        self.serial
            .iter()
            .map(|(g, _)| *g)
            .chain(self.dont_care.iter().cloned())
    }
}

pub struct ValueSummary<V: Clone + PartialEq> {
    dont_care: Option<ExprRef>,
    parallel: Vec<(ExprRef, V)>,
}

impl From<&Node> for ValueSummary<NodeId> {
    fn from(value: &Node) -> Self {
        let dont_care = None;
        let values = value
            .transitions
            .iter()
            .map(|t| (t.guard, t.target))
            .collect();
        Self {
            dont_care,
            parallel: values,
        }
    }
}

impl<V: Clone + PartialEq> ValueSummary<V> {
    fn from(ctx: &mut Context, value: NestedIte<V>) -> Self {
        let mut path_condition = ctx.get_true();
        let parallel = value
            .serial
            .into_iter()
            .map(|(guard, v)| {
                let not_guard = ctx.not(guard);
                let parallel_guard = ctx.and(path_condition, guard);
                path_condition = ctx.and(path_condition, not_guard);
                (parallel_guard, v)
            })
            .collect();
        Self {
            dont_care: value.dont_care,
            parallel,
        }
    }

    fn verify(&self, ctx: &mut Context, smt: &mut SmtLibSolverCtx) -> bool {
        smt.push().unwrap();

        // check that all guards together make true
        let guards: Vec<_> = self.all_guards().collect();
        let any_guard_true = reduce_or(ctx, guards.iter().cloned());
        let not_any_guard_true = ctx.not(any_guard_true);
        if smt.check_sat_assuming(ctx, [not_any_guard_true]).unwrap() != CheckSatResponse::Unsat {
            // guards may not be total
            return false;
        }

        // are all guards mutually exclusive?
        for a in 0..guards.len() {
            for b in 0..guards.len() {
                if a > b {
                    let both_true = ctx.and(guards[a], guards[b]);
                    if smt.check_sat_assuming(ctx, [not_any_guard_true]).unwrap()
                        != CheckSatResponse::Unsat
                    {
                        // guards may not be total
                        return false;
                    }
                }
            }
        }

        smt.pop().unwrap();
        true
    }

    fn all_guards(&self) -> impl Iterator<Item = ExprRef> {
        self.parallel
            .iter()
            .map(|(g, _)| *g)
            .chain(self.dont_care.iter().cloned())
    }
}

/// src: https://github.com/calyxir/calyx/blob/88cc724c60f36dfcde112b7e8e555b307c09053a/calyx/opt/src/passes/simplify_guards.rs#L95
pub fn simplify(ctx: &Context, e: ExprRef) -> ExprRef {
    let bexpr = to_bool_expr(ctx, e);
    let sop = bexpr.clone().simplify_via_bdd();

    todo!("{bexpr:?} {sop:?}")
}

fn to_bool_expr(ctx: &Context, e: ExprRef) -> BExpr<ExprRef> {
    patronus::expr::traversal::bottom_up(ctx, e, |ctx, e, children: &[BExpr<ExprRef>]| {
        match &ctx[e] {
            Expr::BVLiteral(v) if v.is_true() => BExpr::Const(true),
            Expr::BVLiteral(v) if v.is_false() => BExpr::Const(false),
            Expr::BVNot(_, w) if *w == 1 => BExpr::not(children[0].clone()),
            Expr::BVAnd(_, _, w) if *w == 1 => BExpr::and(children[0].clone(), children[1].clone()),
            Expr::BVOr(_, _, w) if *w == 1 => BExpr::or(children[0].clone(), children[1].clone()),
            _ => BExpr::Terminal(e),
        }
    })
}

fn reduce_or(ctx: &mut Context, items: impl Iterator<Item = ExprRef>) -> ExprRef {
    items
        .into_iter()
        .fold(ctx.get_false(), |a, b| or(ctx, a, b))
}

/// optimizing or
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
