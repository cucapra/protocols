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
    pub metadata: SecondaryMap<ExprId, (usize, usize, usize)>,
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
        let metadata: SecondaryMap<ExprId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            name,
            args: Vec::default(),
            body: skip_id,
            type_args: Vec::default(),
            exprs,
            dont_care_id,
            stmts,
            skip_id,
            metadata,
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

    pub fn expr_ids(&self) -> Vec<ExprId> {
        self.exprs.keys().collect()
    }

    pub fn stmt_ids(&self) -> Vec<StmtId> {
        self.stmts.keys().collect()
    }

    pub fn add_expr_md(&mut self, expr_id: ExprId, start: usize, end: usize, fileid: usize) {
        self.metadata[expr_id] = (start, end, fileid);
    }

    pub fn get_expr_md(&self, expr_id: ExprId) -> Option<(usize, usize, usize)> {
        self.metadata.get(expr_id).copied()
    }

    pub fn add_stmt_md(&mut self, expr_id: StmtId, start: usize, end: usize, fileid: usize) {
        todo!()
    }

    pub fn get_stmt_md(&self, expr_id: StmtId) -> Option<(usize, usize, usize)> {
        todo!()
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
            (Type::BitVec(_), Type::BitVec(_)) => true,
            (Type::Struct(id1), Type::Struct(id2)) => id1 == id2,
            (Type::Unknown, _) | (_, Type::Unknown) => true,
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
pub(crate) mod tests {
    use super::*;
    use crate::diagnostic::DiagnosticHandler;

    pub fn build_add_transaction() -> (DiagnosticHandler, SymbolTable, Transaction) {
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

        let dut = symbols.add_without_parent("DUT".to_string(), Type::Struct(add_struct));

        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        let dut_b = symbols.add_with_parent("b".to_string(), dut);
        let dut_s = symbols.add_with_parent("s".to_string(), dut);
        assert_eq!(symbols["DUT.s"], symbols[dut_s]);
        assert_eq!(symbols["s"], symbols[s]);

        // 2) create transaction
        let mut add = Transaction::new("add".to_string());
        add.args = vec![
            Arg::new(a, Dir::In),
            Arg::new(b, Dir::In),
            Arg::new(s, Dir::Out),
        ];
        add.type_args = vec![dut];

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

        (DiagnosticHandler::new(), symbols, add)
    }

    pub fn build_calyx_go_done_transaction() -> (DiagnosticHandler, SymbolTable, Transaction) {
        // Manually create the expected result of parsing `calyx_go_down`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler = DiagnosticHandler::new();
        let ii = symbols.add_without_parent("ii".to_string(), Type::BitVec(32));
        let oo = symbols.add_without_parent("oo".to_string(), Type::BitVec(32));
        assert_eq!(symbols["oo"], symbols[oo]);

        // declare Calyx struct
        let dut_struct = symbols.add_struct(
            "Calyx".to_string(),
            vec![
                Field::new("ii".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("go".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("done".to_string(), Dir::Out, Type::BitVec(1)),
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

        // create fileid and read file
        let input = std::fs::read_to_string("tests/calyx_go_done.prot").expect("failed to load");
        let calyx_fileid = handler.add_file("calyx_go_done.prot".to_string(), input);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];
        calyx_go_done.type_args = vec![dut];

        // 3) create expressions
        let test = symbols.add_without_parent("test".to_string(), Type::Unknown);
        let test_expr = calyx_go_done.e(Expr::Sym(test));

        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        calyx_go_done.add_expr_md(ii_expr, 153, 155, calyx_fileid);
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        calyx_go_done.add_expr_md(dut_oo_expr, 260, 266, calyx_fileid);
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        calyx_go_done.add_expr_md(one_expr, 170, 171, calyx_fileid);
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        calyx_go_done.add_expr_md(zero_expr, 232, 233, calyx_fileid);
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        calyx_go_done.add_expr_md(dut_done_expr, 184, 192, calyx_fileid);
        let cond_expr = calyx_go_done.e(Expr::Equal(dut_done_expr, test_expr));
        calyx_go_done.add_expr_md(cond_expr, 183, 198, calyx_fileid);
        let not_expr = calyx_go_done.e(Expr::Not(cond_expr));
        calyx_go_done.add_expr_md(not_expr, 182, 198, calyx_fileid);

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let dut_ii_assign = calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr));
        calyx_go_done.add_stmt_md(dut_ii_assign, 143, 157, calyx_fileid);
        let dut_go_assign = calyx_go_done.s(Stmt::Assign(dut_go, one_expr));
        calyx_go_done.add_stmt_md(dut_go_assign, 160, 172, calyx_fileid);
        let dut_while = calyx_go_done.s(Stmt::While(not_expr, wbody));
        calyx_go_done.add_stmt_md(dut_while, 175, 219, calyx_fileid);
        let dut_go_reassign = calyx_go_done.s(Stmt::Assign(dut_go, zero_expr));
        calyx_go_done.add_stmt_md(dut_go_reassign, 222, 234, calyx_fileid);
        let dut_ii_dontcare = calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care()));
        calyx_go_done.add_stmt_md(dut_ii_dontcare, 238, 250, calyx_fileid);
        let oo_assign = calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr));
        calyx_go_done.add_stmt_md(oo_assign, 254, 268, calyx_fileid);
        let body = vec![
            dut_ii_assign,
            dut_go_assign,
            dut_while,
            dut_go_reassign,
            dut_ii_dontcare,
            oo_assign,
        ];
        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));

        (handler, symbols, calyx_go_done)
    }

    pub fn build_easycond_transaction() -> (DiagnosticHandler, SymbolTable, Transaction) {
        // Manually create the expected result of parsing `easycond.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler = DiagnosticHandler::new();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(32));
        assert_eq!(symbols["b"], symbols[b]);

        // declare DUT struct (TODO: Fix struct)
        let dut_struct = symbols.add_struct(
            "Adder".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("s".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );
        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        assert_eq!(symbols["dut.a"], symbols[dut_a]);

        // 2) create transaction
        let mut easycond = Transaction::new("easycond".to_string());
        easycond.args = vec![Arg::new(a, Dir::In), Arg::new(b, Dir::Out)];

        // 3) create expressions
        let a_expr = easycond.e(Expr::Sym(a));
        let dut_a_expr = easycond.e(Expr::Sym(dut_a));
        let one_expr = easycond.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let cond_expr = easycond.e(Expr::Equal(dut_a_expr, one_expr));

        // 4) create statements
        let if_body = vec![easycond.s(Stmt::Step)];
        let ifbody = easycond.s(Stmt::Block(if_body));

        let else_body = vec![easycond.s(Stmt::Fork)];
        let elsebody = easycond.s(Stmt::Block(else_body));

        let body = vec![
            easycond.s(Stmt::Assign(dut_a, a_expr)),
            easycond.s(Stmt::IfElse(cond_expr, ifbody, elsebody)),
            easycond.s(Stmt::Assign(b, one_expr)),
        ];
        easycond.body = easycond.s(Stmt::Block(body));
        (handler, symbols, easycond)
    }

    #[test]
    fn create_add_transaction() {
        build_add_transaction();
    }

    #[test]
    fn create_calyx_go_done_transaction() {
        build_calyx_go_done_transaction();
    }

    #[test]
    fn create_easycond_transaction() {
        build_easycond_transaction();
    }
}
