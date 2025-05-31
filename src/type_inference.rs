// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use crate::ir::{BinOp, Expr, ExprId, Stmt, StmtId};
use crate::ir::{SymbolTable, Transaction, Type};
use baa::BitVecOps;
use baa::WidthInt;
use std::cmp;
use std::collections::HashMap;

/// A type‐variable is just an integer ID.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeVar(pub usize);

/// A constraint on widths:
#[derive(Debug, Clone)]
pub enum Constraint {
    /// two widths must be equal
    Eq(TypeVar, TypeVar),
    /// a variable must have at least this many bits
    LowerBound(TypeVar, WidthInt),
    /// a variable must have at most this many bits
    UpperBound(TypeVar, WidthInt),
}

/// During inference we accumulate:
pub struct TypeContext {
    /// next fresh `TypeVar` to hand out
    next_var: usize,

    /// for each expression node, the type‐variable we assigned it
    pub expr_ty: HashMap<ExprId, TypeVar>,

    /// all the constraints we’ve generated
    pub constraints: Vec<Constraint>,

    pub st: SymbolTable,
    pub tr: Transaction,
}

impl TypeContext {
    pub fn new(st: SymbolTable, tr: Transaction) -> Self {
        Self {
            next_var: 0,
            expr_ty: HashMap::new(),
            constraints: Vec::new(),
            st,
            tr,
        }
    }

    /// allocate a fresh type‐variable
    fn fresh(&mut self) -> TypeVar {
        let v = TypeVar(self.next_var);
        self.next_var += 1;
        v
    }

    pub fn constrain_by_expr(&mut self, expr_id: ExprId) -> TypeVar {
        if let Some(&tv) = self.expr_ty.get(&expr_id) {
            return tv;
        }

        let this_tv = self.fresh();
        self.expr_ty.insert(expr_id, this_tv);

        match &self.tr[expr_id].clone() {
            Expr::Const(num) => {
                // take max with 1, in case num is 0
                let min_bits = cmp::max(num.min_width() as WidthInt, 1);
                println!("lower bound for const {:?}: {}", num, min_bits);
                self.constraints
                    .push(Constraint::LowerBound(this_tv, min_bits));
            }

            Expr::Sym(sym) => {
                let tpe = self.st[sym].tpe();
                let width = match tpe {
                    Type::BitVec(w) => w as WidthInt,
                    _ => panic!("symbol {} has non-bitvec type {:?}", sym, tpe),
                };
                // exact‐width for symbols:
                self.constraints
                    .push(Constraint::LowerBound(this_tv, width));
                self.constraints
                    .push(Constraint::UpperBound(this_tv, width));
            }

            Expr::DontCare => {
                // unconstrained
            }

            Expr::Binary(binop, left, right) => {
                // for a binop, arguments must be equal width
                let l_tv = self.constrain_by_expr(left.clone());
                let r_tv = self.constrain_by_expr(right.clone());
                self.constraints.push(Constraint::Eq(l_tv, r_tv));

                match binop {
                    BinOp::And => {
                        // AND is exactly as wide as its arguments
                        self.constraints.push(Constraint::Eq(this_tv, l_tv));
                        self.constraints.push(Constraint::Eq(this_tv, r_tv));
                    }
                    BinOp::Equal => {
                        // EQUAL results in a single bit
                        self.constraints.push(Constraint::LowerBound(this_tv, 1));
                        self.constraints.push(Constraint::UpperBound(this_tv, 1));
                    }
                }
            }

            Expr::Unary(_, sub) => {
                // which unary op it is doesn't matter for width inference
                let s_tv = self.constrain_by_expr(sub.clone());
                self.constraints.push(Constraint::Eq(this_tv, s_tv));
            }

            Expr::Slice(inner, high, low) => {
                let inner_tv = self.constrain_by_expr(inner.clone());
                let slice_w = (high - low + 1) as WidthInt;

                // inner must be at least high+1 bits
                self.constraints
                    .push(Constraint::LowerBound(inner_tv, (high + 1) as WidthInt));

                // slice result is exactly slice_w
                self.constraints
                    .push(Constraint::LowerBound(this_tv, slice_w));
                self.constraints
                    .push(Constraint::UpperBound(this_tv, slice_w));
            }
        }

        this_tv
    }

    pub fn constrain_by_stmt(&mut self, stmt_id: StmtId) {
        if let Stmt::Assign(lhs, rhs) = self.tr[stmt_id] {
            let tpe = self.st[lhs].tpe();
            let width = match tpe {
                Type::BitVec(w) => w as WidthInt,
                _ => panic!("symbol {} has non-bitvec type {:?}", lhs, tpe),
            };

            let rhs_tv = self.constrain_by_expr(rhs);

            // exact‐width assertion on RHS
            self.constraints.push(Constraint::LowerBound(rhs_tv, width));
            self.constraints.push(Constraint::UpperBound(rhs_tv, width));
        }
    }

    /// Solve all constraints, erroring on any lower>upper conflict.
    fn solve(&self) -> Result<HashMap<TypeVar, WidthInt>, String> {
        // our type vars are just integers, so union find from 1 to next_var
        // which is precisely the number of type vars we have
        let mut uf = UnionFind::new(self.next_var);

        // merge all type vars on equality constraints
        for c in &self.constraints {
            if let Constraint::Eq(a, b) = *c {
                uf.union(a.0, b.0);
            }
        }

        // collect all the bounds per union-find class
        // these map the parent of each class to a vector of lower and upper bound widths
        let mut lowers: HashMap<usize, Vec<WidthInt>> = HashMap::new();
        let mut uppers: HashMap<usize, Vec<WidthInt>> = HashMap::new();

        for c in self.constraints.clone() {
            match c {
                Constraint::LowerBound(tv, lo) => {
                    lowers.entry(uf.find(tv.0)).or_default().push(lo);
                }
                Constraint::UpperBound(tv, hi) => {
                    uppers.entry(uf.find(tv.0)).or_default().push(hi);
                }
                _ => {}
            }
        }

        // determine final width
        let mut class_w = HashMap::new();
        for root in 0..self.next_var {
            // lowers and uppers are only keyed by the root, so ignore everything else
            if uf.find(root) != root {
                continue;
            }

            // stealing terms from real analysis lol
            let infimum = lowers
                .get(&root)
                .and_then(|v| v.iter().max().cloned())
                .unwrap_or(1);
            let supremum = uppers
                .get(&root)
                .and_then(|v| v.iter().min().cloned())
                .unwrap_or(WidthInt::MAX);

            if infimum > supremum {
                return Err(format!(
                    "Width conflict in class {}: lower-bound {} > upper-bound {}",
                    root, infimum, supremum
                ));
            }

            // TODO: always choose the infimum?
            let w = infimum;
            class_w.insert(root, w);
        }

        // map type var to final chosen width
        let mut result = HashMap::new();
        for i in 0..self.next_var {
            let w = class_w[&uf.find(i)];
            result.insert(TypeVar(i), w);
        }

        Ok(result)
    }

    pub fn finalize(&mut self) -> HashMap<ExprId, WidthInt> {
        // calculate all type constraints
        for expr_id in self.tr.expr_ids() {
            self.constrain_by_expr(expr_id);
        }

        for stmt_id in self.tr.stmt_ids() {
            self.constrain_by_stmt(stmt_id);
        }

        // solve type constraints
        let solved_constraints = self.solve().unwrap_or_else(|_| {
            panic!(
                "Failed to solve type constraints for transaction: {}",
                self.tr.name
            )
        });

        // map from expr_id to usize width
        // FIXME: This is kinda inefficient
        let mut expr_widths: HashMap<ExprId, WidthInt> = HashMap::new();
        for (type_var, width) in solved_constraints {
            // map type_var to expr_id
            if let Some(expr_id) =
                self.expr_ty.iter().find_map(
                    |(&id, &tv)| {
                        if tv == type_var {
                            Some(id)
                        } else {
                            None
                        }
                    },
                )
            {
                expr_widths.insert(expr_id, width);
            }
        }

        expr_widths
    }
}

struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

// TODO: is there a crate that does this better?
// Inspired by https://geeksforgeeks.org/union-by-rank-and-path-compression-in-union-find-algorithm/
impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            // initialize so that all nodes are their own parent
            parent: (0..n).collect(),
            rank: vec![0; n], // ranks all are 0 at first
        }
    }

    fn find(&mut self, x: usize) -> usize {
        // stop once the parent is itself (i.e.) at the root of the tree
        if self.parent[x] != x {
            let p = self.parent[x];
            self.parent[x] = self.find(p);
        }
        self.parent[x]
    }

    // I think this ensures O(log n) amortized?
    fn union(&mut self, x: usize, y: usize) {
        // find the parent of x
        let parent_x = self.find(x);

        // find the parent of y
        let parent_y = self.find(y);

        // if they are already in the same set (have same parent),
        // we don't need to do anything
        if parent_x == parent_y {
            return;
        }

        // attatch the smaller tree under the larger one
        match self.rank[parent_x].cmp(&self.rank[parent_y]) {
            std::cmp::Ordering::Less => {
                self.parent[parent_x] = parent_y;
            }
            std::cmp::Ordering::Greater => {
                self.parent[parent_y] = parent_x;
            }
            std::cmp::Ordering::Equal => {
                // choose one as the new root arbitrarily
                self.parent[parent_y] = parent_x;
                self.rank[parent_x] += 1;
            }
        }
    }
}
