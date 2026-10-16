//! Per-bit facts and expression evaluation for bit-vector constant propagation.

use baa::{BitVecOps, BitVecValue};
use patronus::expr::{Context, Expr, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

/// Disjoint masks of bits definitely zero and definitely one. Bits in neither
/// mask may be either. This domain supports arbitrary bit-vector widths.
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

    /// Use a condition known to be true and discard cached results that may
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
            // Symbols without supplied facts and unsupported operators are
            // conservatively unknown.
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
