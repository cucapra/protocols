// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::{Context, Expr, ExprRef, StringRef, WidthInt};
use rustc_hash::FxHashMap;
use std::borrow::Cow;
use std::ops::Index;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Transaction {
    name: StringRef,
    args: Vec<Arg>,
    body: Vec<Stmt>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Arg {
    dir: Dir,
    name: StringRef,
    tpe: Type,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Dir {
    In,
    Out,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    BitVec(WidthInt),
    /// Placeholder type for `dut`
    Dut,
    /// Type taken on when we do not know the actual type yet
    Unknown,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Stmt {
    Assign(ExprRef, ExprRef),
    Step,
    Fork,
    While(ExprRef, Vec<Stmt>),
    IfElse(ExprRef, Vec<Stmt>, Vec<Stmt>),
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct SymbolTable {
    entries: Vec<SymbolTableEntry>,
    by_name: FxHashMap<String, u32>,
    by_expr: FxHashMap<ExprRef, u32>,
}

impl SymbolTable {
    pub fn declare(&mut self, name: Cow<str>, tpe: Type) -> ExprRef {
        assert!(
            !self.by_name.contains_key(name.as_ref()),
            "we already have an entry for {}!",
            name.as_ref()
        );
    }
}

impl Index<&str> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &str) -> &Self::Output {
        let index = self.by_name[index];
        &self.entries[index as usize]
    }
}

impl Index<ExprRef> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: ExprRef) -> &Self::Output {
        let index = self.by_expr[index];
        &self.entries[index as usize]
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SymbolTableEntry {
    name: StringRef,
    tpe: Type,
    parent: ExprRef,
    next: ExprRef,
}

impl SymbolTableEntry {
    pub fn name(&self, ctx: &Context) -> &str {
        &ctx[self.name]
    }

    pub fn tpe(&self) -> Type {
        self.tpe.clone()
    }
}
