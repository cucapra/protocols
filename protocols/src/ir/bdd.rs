// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! BDD-based simplification for patronus expressions

use boolean_expression::Expr as BExpr;
use patronus::expr::{Context, Expr, ExprRef};
use rustc_hash::FxHashMap;

/// src: https://github.com/calyxir/calyx/blob/88cc724c60f36dfcde112b7e8e555b307c09053a/calyx/opt/src/passes/simplify_guards.rs#L95
pub fn simplify(ctx: &Context, e: ExprRef) -> ExprRef {
    let bexpr = to_bool_expr(ctx, e);
    let sop = bexpr.simplify_via_bdd();

    todo!("{bexpr:?} {sop:?}")
}

fn to_bool_expr(ctx: &Context, e: ExprRef) -> BExpr<ExprRef> {
    patronus::expr::traversal::bottom_up(ctx, e, |ctx, e, children| match &ctx[e] {
        Expr::BVLiteral(v) if v.is_true() => BExpr::Const(true),
        Expr::BVLiteral(v) if v.is_false() => BExpr::Const(false),
        Expr::BVNot(_, w) if *w == 1 => BExpr::not(children[0]),
        Expr::BVAnd(_, _, w) if *w == 1 => BExpr::and(children[0], children[1]),
        Expr::BVOr(_, _, w) if *w == 1 => BExpr::or(children[0], children[1]),
        _ => BExpr::Terminal(e),
    })
}
