// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use baa::BitVecValue;
use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};
use rustc_hash::FxHashMap;
use std::ops::Index;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub name: String,
    pub args: Vec<Arg>,
    pub body: StmtId,
    pub type_args: Vec<SymbolId>,
    exprs: PrimaryMap<ExprId, Expr>,
    dont_care_id: ExprId,
    stmts: PrimaryMap<StmtId, Stmt>,
    skip_id: StmtId,
    expr_loc: SecondaryMap<ExprId, (usize, usize, usize)>,
    stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)>,
}

impl Transaction {
    pub fn new(name: String) -> Self {
        let mut exprs = PrimaryMap::new();
        let dont_care_id = exprs.push(Expr::DontCare);
        let mut stmts = PrimaryMap::new();
        let skip_id = stmts.push(Stmt::Skip);
        let expr_loc: SecondaryMap<ExprId, (usize, usize, usize)> = SecondaryMap::new();
        let stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            name,
            args: Vec::default(),
            body: skip_id,
            type_args: Vec::default(),
            exprs,
            dont_care_id,
            stmts,
            skip_id,
            expr_loc,
            stmt_loc,
        }
    }

    /// add a new expression to the transaction
    pub fn e(&mut self, expr: Expr) -> ExprId {
        self.exprs.push(expr)
    }

    /// add a new statement to the transaction
    pub fn s(&mut self, stmt: Stmt) -> StmtId {
        self.stmts.push(stmt)
    }

    pub fn expr_dont_care(&self) -> ExprId {
        self.dont_care_id
    }

    pub fn stmt_skip(&self) -> StmtId {
        self.skip_id
    }

    pub fn expr_ids(&self) -> Vec<ExprId> {
        self.exprs.keys().collect()
    }

    pub fn stmt_ids(&self) -> Vec<StmtId> {
        self.stmts.keys().collect()
    }

    pub fn add_expr_loc(&mut self, expr_id: ExprId, start: usize, end: usize, fileid: usize) {
        self.expr_loc[expr_id] = (start, end, fileid);
    }

    pub fn get_expr_loc(&self, expr_id: ExprId) -> Option<(usize, usize, usize)> {
        self.expr_loc.get(expr_id).copied()
    }

    pub fn add_stmt_loc(&mut self, stmt_id: StmtId, start: usize, end: usize, fileid: usize) {
        self.stmt_loc[stmt_id] = (start, end, fileid);
    }

    pub fn get_stmt_loc(&self, stmt_id: StmtId) -> Option<(usize, usize, usize)> {
        self.stmt_loc.get(stmt_id).copied()
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

impl Index<&StmtId> for Transaction {
    type Output = Stmt;

    fn index(&self, index: &StmtId) -> &Self::Output {
        &self.stmts[*index]
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

    pub fn symbol(&self) -> SymbolId {
        self.symbol
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
    Struct(StructId),
    /// Type taken on when we do not know the actual type yet
    Unknown,
}

impl Type {
    pub fn is_equivalent(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::BitVec(vec1), Type::BitVec(vec2)) => vec1 == vec2,
            (Type::Struct(id1), Type::Struct(id2)) => id1 == id2,
            // TODO: type inferencing to infer unknown == LHS
            (Type::Unknown, _) | (_, Type::Unknown) => false,
            _ => false,
        }
    }
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
    AssertEq(ExprId, ExprId),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ExprId(u32);
entity_impl!(ExprId, "expr");

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BinOp {
    Equal,
    And,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr {
    // nullary
    Const(BitVecValue),
    Sym(SymbolId),
    DontCare,
    // unary
    Binary(BinOp, ExprId, ExprId),
    // binary
    Unary(UnaryOp, ExprId),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BoxedExpr {
    // nullary
    Const(BitVecValue),
    Sym(SymbolId),
    DontCare,
    // unary
    Binary(BinOp, Box<BoxedExpr>, Box<BoxedExpr>),
    // binary
    Unary(UnaryOp, Box<BoxedExpr>),
}

// add further bin ops

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StructId(u32);
entity_impl!(StructId, "struct");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Struct {
    name: String,
    pins: Vec<Field>,
}

impl Struct {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn pins(&self) -> &Vec<Field> {
        &self.pins
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    name: String,
    dir: Dir,
    tpe: Type,
}

impl Field {
    pub fn new(name: String, dir: Dir, tpe: Type) -> Self {
        Self { name, dir, tpe }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn dir(&self) -> Dir {
        self.dir
    }

    pub fn tpe(&self) -> Type {
        self.tpe.clone()
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SymbolId(u32);
entity_impl!(SymbolId, "symbol");

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct SymbolTable {
    entries: PrimaryMap<SymbolId, SymbolTableEntry>,
    // FIXME: Use by_name map 
    by_name: FxHashMap<String, SymbolId>,
    structs: PrimaryMap<StructId, Struct>,
}

impl SymbolTable {
    pub fn add_without_parent(&mut self, name: String, tpe: Type) -> SymbolId {
        assert!(
            !name.contains('.'),
            "hierarchical names need to be handled externally"
        );
        let entry = SymbolTableEntry {
            name,
            tpe,
            parent: None,
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

    pub fn symbol_id_from_name(&self, name: &str) -> Option<SymbolId> {
        self.by_name.get(name).copied()
    }

    pub fn add_with_parent(&mut self, name: String, parent: SymbolId) -> SymbolId {
        assert!(
            !name.contains('.'),
            "hierarchical names need to be handled externally"
        );

        let existing_pin: Option<&Field>;

        if let Type::Struct(structid) = self.entries[parent].tpe() {
            let fields = self.structs[structid].pins();
            existing_pin = fields.iter().find(|field| field.name == name);
        } else {
            existing_pin = None;
        }

        let pin_type = match existing_pin {
            Some(pin) => pin.tpe(),
            None => Type::Unknown,
        };

        let entry = SymbolTableEntry {
            name,
            tpe: pin_type,
            parent: Some(parent),
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

    pub fn add_struct(&mut self, name: String, pins: Vec<Field>) -> StructId {
        let s = Struct { name, pins };
        self.structs.push(s)
    }

    pub fn struct_id_from_name(&mut self, name: &str) -> Option<StructId> {
        self.structs.iter().find_map(|(id, s)| {
            if s.name() == name {
                Some(id)
            } else {
                None
            }
        })
    }

    pub fn struct_from_struct_id(&mut self, struct_id: StructId) -> &Struct {
        &self.structs[struct_id]
    }

    pub fn struct_ids(&self) -> Vec<StructId> {
        self.structs.keys().collect()
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

impl Index<StructId> for SymbolTable {
    type Output = Struct;

    fn index(&self, index: StructId) -> &Self::Output {
        &self.structs[index]
    }
}

impl Index<&StructId> for SymbolTable {
    type Output = Struct;

    fn index(&self, index: &StructId) -> &Self::Output {
        &self.structs[*index]
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

    pub fn parent(&self) -> Option<SymbolId> {
        self.parent
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
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(32));
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(32));
        assert_eq!(symbols["s"], symbols[s]);

        // declare Adder struct
        let add_struct = symbols.add_struct(
            "Adder".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("s".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );
        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(add_struct));
        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        let dut_b = symbols.add_with_parent("b".to_string(), dut);
        let dut_s = symbols.add_with_parent("s".to_string(), dut);
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

    #[test]
    fn serialize_calyx_go_done_transaction() {
        // Manually create the expected result of parsing `calyx_go_done`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let ii = symbols.add_without_parent("ii".to_string(), Type::BitVec(32));
        let oo = symbols.add_without_parent("oo".to_string(), Type::BitVec(32));
        assert_eq!(symbols["oo"], symbols[oo]);

        // declare DUT struct
        let dut_struct = symbols.add_struct(
            "Calyx".to_string(),
            vec![
                Field::new("ii".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("go".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("done".to_string(), Dir::Out, Type::BitVec(32)),
                Field::new("oo".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_ii = symbols.add_with_parent("ii".to_string(), dut);
        let dut_go = symbols.add_with_parent("go".to_string(), dut);
        let dut_done = symbols.add_with_parent("done".to_string(), dut);
        let dut_oo = symbols.add_with_parent("oo".to_string(), dut);
        assert_eq!(symbols["dut.oo"], symbols[dut_oo]);
        assert_eq!(symbols["oo"], symbols[oo]);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];
        calyx_go_done.type_args = vec![dut];

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        let cond_expr = calyx_go_done.e(Expr::Binary(BinOp::Equal, dut_done_expr, one_expr));
        let not_expr = calyx_go_done.e(Expr::Unary(UnaryOp::Not, cond_expr));

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let body = vec![
            calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr)),
            calyx_go_done.s(Stmt::Assign(dut_go, one_expr)),
            calyx_go_done.s(Stmt::While(not_expr, wbody)),
            calyx_go_done.s(Stmt::Assign(dut_done, one_expr)),
            calyx_go_done.s(Stmt::Assign(dut_go, zero_expr)),
            calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care())),
            calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr)),
        ];

        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));
    }
}
