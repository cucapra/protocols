// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use cranelift_entity::*;
use std::ops::Index;

pub struct Transaction {
    name: String,
    stmts: PrimaryMap<StmtId, Stmt>,
    exprs: PrimaryMap<ExprId, Expr>,
}

impl Index<StmtId> for Transaction {
    type Output = Stmt;

    fn index(&self, index: StmtId) -> &Self::Output {
        &self.stmts[index]
    }
}

impl Index<ExprId> for Transaction {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct StmtId(u32);
entity_impl!(StmtId, "stmt");

pub enum Stmt {
    Assign(ExprId, ExprId),
    Step,
    Fork,
    While(ExprId),
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct ExprId(u32);
entity_impl!(ExprId, "expr");
pub enum Expr {}
