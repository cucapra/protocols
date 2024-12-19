// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecValue;
use cranelift_entity::{entity_impl, PrimaryMap};
use rustc_hash::FxHashMap;
use std::ops::Index;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Transaction {
    pub name: String,
    pub args: Vec<Arg>,
    pub body: StmtId,
    exprs: PrimaryMap<ExprId, Expr>,
    dont_care_id: ExprId,
    stmts: PrimaryMap<StmtId, Stmt>,
    skip_id: StmtId,
}

impl Transaction {
    pub fn new(name: String) -> Self {
        let mut exprs = PrimaryMap::new();
        let dont_care_id = exprs.push(Expr::DontCare);
        let mut stmts = PrimaryMap::new();
        let skip_id = stmts.push(Stmt::Skip);
        Self {
            name,
            args: Vec::default(),
            body: skip_id,
            exprs,
            dont_care_id,
            stmts,
            skip_id,
        }
    }

    /// add a new expression to the transaction
    pub fn e(&mut self, expr: Expr) -> ExprId {
        self.exprs.push(expr)
    }

    /// add a new statement to the transaction
    pub fn s(&mut self, expr: Stmt) -> StmtId {
        self.stmts.push(expr)
    }

    pub fn expr_dont_care(&self) -> ExprId {
        self.dont_care_id
    }

    pub fn stmt_skip(&self) -> StmtId {
        self.skip_id
    }
}

impl Index<ExprId> for Transaction {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

impl Index<&ExprId> for Transaction {
    type Output = Expr;

    fn index(&self, index: &ExprId) -> &Self::Output {
        &self.exprs[*index]
    }
}

impl Index<StmtId> for Transaction {
    type Output = Stmt;

    fn index(&self, index: StmtId) -> &Self::Output {
        &self.stmts[index]
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Arg {
    dir: Dir,
    symbol: SymbolId,
}

impl Arg {
    pub fn dir(&self) -> Dir {
        self.dir
    }

    pub fn new(symbol: SymbolId, dir: Dir) -> Self {
        Self { dir, symbol }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Dir {
    In,
    Out,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    BitVec(u32),
    /// Placeholder type for `dut`
    Dut,
    /// Type taken on when we do not know the actual type yet
    Unknown,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StmtId(u32);
entity_impl!(StmtId, "stmt");

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Stmt {
    Skip,
    Block(Vec<StmtId>),
    Assign(SymbolId, ExprId),
    Step,
    Fork,
    While(ExprId, StmtId),
    IfElse(ExprId, StmtId, StmtId),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ExprId(u32);
entity_impl!(ExprId, "expr");

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr {
    // nullary
    Const(BitVecValue),
    Sym(SymbolId),
    DontCare,
    // unary
    Not(ExprId),
    // binary
    And(ExprId, ExprId),
    Equal(ExprId, ExprId),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SymbolId(u32);
entity_impl!(SymbolId, "symbol");

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct SymbolTable {
    entries: PrimaryMap<SymbolId, SymbolTableEntry>,
    by_name: FxHashMap<String, SymbolId>,
}

impl SymbolTable {
    pub fn add(&mut self, name: String, tpe: Type, parent: Option<SymbolId>) -> SymbolId {
        assert!(
            !name.contains('.'),
            "hierarchical names need to be handled externally"
        );
        let entry = SymbolTableEntry {
            name,
            tpe,
            parent,
            next: None,
        };
        let lookup_name = entry.full_name(self);

        assert!(
            !self.by_name.contains_key(&lookup_name),
            "we already have an entry for {lookup_name}!",
        );

        let id = self.entries.push(entry);
        self.by_name.insert(lookup_name, id);
        id
    }
}

impl Index<&str> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &str) -> &Self::Output {
        let index = self.by_name[index];
        &self.entries[index]
    }
}

impl Index<SymbolId> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: SymbolId) -> &Self::Output {
        &self.entries[index]
    }
}

impl Index<&SymbolId> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &SymbolId) -> &Self::Output {
        &self.entries[*index]
    }
}

impl Index<Arg> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: Arg) -> &Self::Output {
        &self.entries[index.symbol]
    }
}

impl Index<&Arg> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &Arg) -> &Self::Output {
        &self.entries[index.symbol]
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SymbolTableEntry {
    name: String,
    tpe: Type,
    parent: Option<SymbolId>,
    next: Option<SymbolId>,
}

impl SymbolTableEntry {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn tpe(&self) -> Type {
        self.tpe.clone()
    }

    /// full hierarchical name
    pub fn full_name(&self, symbols: &SymbolTable) -> String {
        let mut name = self.name.clone();
        let mut parent = self.parent;
        while let Some(p) = parent {
            let parent_entry = &symbols[p];
            name = format!("{}.{name}", parent_entry.name);
            parent = parent_entry.parent;
        }
        name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_add_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let a = symbols.add("a".to_string(), Type::BitVec(32), None);
        let b = symbols.add("b".to_string(), Type::BitVec(32), None);
        let s = symbols.add("s".to_string(), Type::BitVec(32), None);
        assert_eq!(symbols["s"], symbols[s]);
        let dut = symbols.add("dut".to_string(), Type::Dut, None);
        let dut_a = symbols.add("a".to_string(), Type::Unknown, Some(dut));
        let dut_b = symbols.add("b".to_string(), Type::Unknown, Some(dut));
        let dut_s = symbols.add("s".to_string(), Type::Unknown, Some(dut));
        assert_eq!(symbols["dut.s"], symbols[dut_s]);
        assert_eq!(symbols["s"], symbols[s]);

        // 2) create transaction
        let mut add = Transaction::new("add".to_string());
        add.args = vec![
            Arg::new(a, Dir::In),
            Arg::new(b, Dir::In),
            Arg::new(s, Dir::Out),
        ];

        // 3) create expressions
        let a_expr = add.e(Expr::Sym(a));
        let b_expr = add.e(Expr::Sym(b));
        let dut_s_expr = add.e(Expr::Sym(dut_s));

        // 4) create statements
        let body = vec![
            add.s(Stmt::Assign(dut_a, a_expr)),
            add.s(Stmt::Assign(dut_b, b_expr)),
            add.s(Stmt::Step),
            add.s(Stmt::Fork),
            add.s(Stmt::Assign(dut_a, add.expr_dont_care())),
            add.s(Stmt::Assign(dut_b, add.expr_dont_care())),
            add.s(Stmt::Assign(s, dut_s_expr)),
        ];
        add.body = add.s(Stmt::Block(body));
    }
}
