// Copyright 2024-26 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use std::ops::{Deref, DerefMut, Index};

use baa::BitVecValue;
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use rustc_hash::{FxHashMap, FxHashSet};
use strum::IntoEnumIterator;

use crate::frontend::serialize::{build_statements, serialize_expr};
use crate::frontend::symbol::{
    Arg, Dir, INVALID_SYMBOL_ID, ScopeId, StructId, SymbolId, SymbolTable, Type,
};

/// Frontend representation of parsed protocol files.
#[derive(Debug, Clone)]
pub struct Ast {
    pub st: SymbolTable,
    pub protos: Vec<Protocol>,
    pub remaps: Vec<RemapModule>,
}

#[derive(Debug, Clone)]
pub struct ProtocolContext {
    /// The name of the `Protocol`
    pub name: String,

    /// List of `Arg`s to the `Protocol`
    pub args: Vec<Arg>,

    /// type parameter symbol
    pub dut_sym: SymbolId,

    /// Whether the protocol has been marked as `idle` with `#[idle]`
    pub is_idle: bool,

    /// Maps `ExprId`s to their corresponding `Expr`s
    exprs: PrimaryMap<ExprId, Expr>,

    /// The distinguished `ExprId` corresponding to `DontCare`
    dont_care_id: ExprId,

    true_expr_id: ExprId,

    expr_loc: SecondaryMap<ExprId, (usize, usize, usize)>,

    /// The scope in the [[SymbolTable]] associated with this protocol.
    pub scope: ScopeId,
}

#[cfg(test)]
fn assert_proto_ctx_eq(a: &ProtocolContext, b: &ProtocolContext) {
    assert_eq!(a.name, b.name, "{a:?}\n{b:?}");
    assert_eq!(a.args, b.args, "{a:?}\n{b:?}");
    assert_eq!(a.dut_sym, b.dut_sym, "{a:?}\n{b:?}");
    assert_eq!(a.is_idle, b.is_idle, "{a:?}\n{b:?}");
    // TODO: expression comparison does not work
    // assert_eq!(a.exprs, b.exprs, "{a:?}\n{b:?}");
    assert_eq!(a.dont_care_id, b.dont_care_id, "{a:?}\n{b:?}");
    assert_eq!(a.true_expr_id, b.true_expr_id, "{a:?}\n{b:?}");
    assert_eq!(a.scope, b.scope, "{a:?}\n{b:?}");
    // we intentionally do not compare the expression locations
}

impl ProtocolContext {
    pub fn new(name: String, scope: ScopeId) -> Self {
        let mut exprs = PrimaryMap::new();
        let dont_care_id = exprs.push(Expr::DontCare);
        let true_expr_id = exprs.push(Expr::Const(BitVecValue::new_true()));
        let expr_loc: SecondaryMap<ExprId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            name,
            args: Vec::default(),
            dut_sym: INVALID_SYMBOL_ID,
            is_idle: false,
            exprs,
            dont_care_id,
            true_expr_id,
            expr_loc,
            scope,
        }
    }

    pub fn e(&mut self, expr: Expr) -> ExprId {
        self.exprs.push(expr)
    }

    pub fn expr_dont_care(&self) -> ExprId {
        self.dont_care_id
    }

    pub fn expr_true(&self) -> ExprId {
        self.true_expr_id
    }

    pub fn expr_ids(&self) -> Vec<ExprId> {
        self.exprs.keys().collect()
    }

    pub fn add_expr_loc(&mut self, expr_id: ExprId, start: usize, end: usize, fileid: usize) {
        self.expr_loc[expr_id] = (start, end, fileid);
    }

    pub fn get_expr_loc(&self, expr_id: ExprId) -> Option<(usize, usize, usize)> {
        self.expr_loc.get(expr_id).copied()
    }

    pub fn exprs_clone(&self) -> PrimaryMap<ExprId, Expr> {
        self.exprs.clone()
    }

    pub fn dont_care_id(&self) -> ExprId {
        self.dont_care_id
    }

    pub fn expr_loc_clone(&self) -> SecondaryMap<ExprId, (usize, usize, usize)> {
        self.expr_loc.clone()
    }

    pub fn dut_struct(&self, st: &SymbolTable) -> StructId {
        if let Type::Struct(struct_id) = st[self.dut_sym].tpe() {
            struct_id
        } else {
            unreachable!("DUT must always be a struct")
        }
    }

    pub fn dut_pins(&self, st: &SymbolTable) -> impl Iterator<Item = SymbolId> {
        st.get_children(&self.dut_sym)
    }

    pub fn dut_input_symbols(&self, st: &SymbolTable) -> impl Iterator<Item = SymbolId> {
        self.dut_pins(st).filter(|sym| st[sym].is_in_port())
    }
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct Module {
//     clock: Clock,
//     protocols: Vec<Protocol>,
//     ports: Vec<Field>,
// }
//
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Clock {
    #[default]
    None,
    Posedge(String),
}

/// Represents an unresolved `module`.
#[derive(Debug, Clone)]
pub struct RemapModule {
    pub ctx: ProtocolContext,
    pub name: String,
    pub clock: Clock,
    pub implements: Vec<StructId>,
    pub mappings: Vec<Mapping>,
}

#[cfg(test)]
pub(crate) fn assert_remap_eq(a: &RemapModule, b: &RemapModule) {
    assert_proto_ctx_eq(&a.ctx, &b.ctx);
    assert_eq!(a.name, b.name);
    assert_eq!(a.clock, b.clock);
    assert_eq!(a.implements, b.implements);
    assert_eq!(a.mappings, b.mappings);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mapping {
    pub name: String,
    pub dir: Dir,
    pub tpe: Type,
    pub rhs: ExprId,
    pub cond: ExprId,
}

#[derive(Debug, Clone)]
pub struct Protocol {
    pub ctx: ProtocolContext,

    /// The body of the `Protocol`, identified by its `StmtId`
    pub body: StmtId,

    /// Maps `StmtId`s to their corresponding `Stmt`s
    stmts: PrimaryMap<StmtId, Stmt>,
    stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)>,
}

#[cfg(test)]
pub(crate) fn assert_proto_eq(a: &Protocol, b: &Protocol) {
    assert_eq!(a.body, b.body);
    assert_eq!(a.stmts, b.stmts);
    // we do not compare the statement locations
    assert_proto_ctx_eq(&a.ctx, &b.ctx);
}

impl Protocol {
    pub fn new(name: String, scope: ScopeId) -> Self {
        let mut stmts = PrimaryMap::new();
        let block_id: StmtId = stmts.push(Stmt::Block(vec![]));
        let stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            ctx: ProtocolContext::new(name, scope),
            body: block_id,
            stmts,
            stmt_loc,
        }
    }

    /// an empty Protocol AST with a given ProtocolContext `ctx`
    pub fn from_context(ctx: ProtocolContext) -> Self {
        let mut stmts = PrimaryMap::new();
        let block_id: StmtId = stmts.push(Stmt::Block(vec![]));
        let stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            ctx,
            body: block_id,
            stmts,
            stmt_loc,
        }
    }

    /// add a new expression to the transaction
    pub fn e(&mut self, expr: Expr) -> ExprId {
        self.ctx.exprs.push(expr)
    }

    /// add a new statement to the transaction
    pub fn s(&mut self, stmt: Stmt) -> StmtId {
        self.stmts.push(stmt)
    }

    pub fn expr_dont_care(&self) -> ExprId {
        self.ctx.expr_dont_care()
    }

    pub fn expr_ids(&self) -> Vec<ExprId> {
        self.ctx.expr_ids()
    }

    pub fn stmt_ids(&self) -> Vec<StmtId> {
        self.stmts.keys().collect()
    }

    pub fn add_expr_loc(&mut self, expr_id: ExprId, start: usize, end: usize, fileid: usize) {
        self.ctx.add_expr_loc(expr_id, start, end, fileid);
    }

    pub fn get_expr_loc(&self, expr_id: ExprId) -> Option<(usize, usize, usize)> {
        self.ctx.get_expr_loc(expr_id)
    }

    pub fn add_stmt_loc(&mut self, stmt_id: StmtId, start: usize, end: usize, fileid: usize) {
        self.stmt_loc[stmt_id] = (start, end, fileid);
    }

    pub fn get_stmt_loc(&self, stmt_id: StmtId) -> Option<(usize, usize, usize)> {
        self.stmt_loc.get(stmt_id).copied()
    }

    pub fn next_stmt_mapping(&self) -> FxHashMap<StmtId, Option<StmtId>> {
        self.next_stmt_mapping_helper(self.body, None)
    }

    /// comma separated string of all constructs used
    pub fn used_constructs(&self) -> String {
        let used: FxHashSet<_> = self
            .stmts
            .iter()
            .map(|(_, stmt)| StmtDiscriminants::from(stmt))
            .collect();

        // print out all the Stmt types used (except for block, because every protocol has a block
        // and it's a purely internal-facing construct)
        StmtDiscriminants::iter()
            .filter(|construct| *construct != StmtDiscriminants::Block)
            .filter(|construct| used.contains(construct))
            .map(|construct| construct.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn next_stmt_mapping_helper(
        &self,
        block_id: StmtId,
        stmt_after_block: Option<StmtId>,
    ) -> FxHashMap<StmtId, Option<StmtId>> {
        // Precondition: input StmtId refers to the a Stmt::Block variant
        let mut map = FxHashMap::default();

        if let Stmt::Block(stmts) = &self.stmts[block_id] {
            // Handle empty blocks by mapping them directly to stmt_after_block
            if stmts.is_empty() {
                map.insert(block_id, stmt_after_block);
            }

            for (i, &stmt_id) in stmts.iter().enumerate() {
                let mut new_stmt_after_block = stmt_after_block;
                if i == stmts.len() - 1 {
                    // check if we're at the end of the block
                    map.insert(stmt_id, stmt_after_block);
                } else {
                    // println!("mapping {} -> {}", stmt_id, stmts[i + 1]);
                    map.insert(stmt_id, Some(stmts[i + 1]));
                    new_stmt_after_block = Some(stmts[i + 1]);
                }

                match &self.stmts[stmt_id] {
                    Stmt::Block(_) => {
                        map.extend(self.next_stmt_mapping_helper(stmt_id, new_stmt_after_block));
                    }
                    Stmt::IfElse(_, then_stmt_id, else_stmt_id) => {
                        map.extend(
                            self.next_stmt_mapping_helper(*then_stmt_id, new_stmt_after_block),
                        );
                        map.extend(
                            self.next_stmt_mapping_helper(*else_stmt_id, new_stmt_after_block),
                        );
                    }
                    // Add a back-edge from the loop body to the current `stmt_id`
                    Stmt::RepeatLoop(_, body_id)
                    | Stmt::While(_, body_id)
                    | Stmt::ForInLoop(_, _, body_id) => {
                        map.extend(self.next_stmt_mapping_helper(*body_id, Some(stmt_id)));
                    }
                    _ => {}
                }
            }
        } else {
            panic!("Precondition: input StmtId refers to the a Stmt::Block variant was violated.");
        }

        map
    }

    /// Extracts the types of the arguments for a transaction, using the
    /// provided `symbol_table` to look up `SymbolId`s
    pub fn get_arg_types(&self, symbol_table: &SymbolTable) -> Vec<Type> {
        let mut arg_types = vec![];
        for arg in &self.args {
            let symbol_id = arg.symbol();
            let symbol_table_entry = &symbol_table[symbol_id];
            arg_types.push(symbol_table_entry.tpe())
        }
        arg_types
    }

    /// Determines if `symbol_id` is a function parameter with the desired `direction`
    /// (e.g. check if an identifier corresponds to an input parameter of the function)
    pub fn is_param(&self, symbol_id: SymbolId) -> bool {
        self.args.iter().any(|a| a.symbol() == symbol_id)
    }

    /// Pretty-prints an `Expr` based on its `ExprId`, using the
    /// provided `SymbolTable` to look up `SymbolId`s
    pub fn format_expr(&self, expr_id: &ExprId, symbol_table: &SymbolTable) -> String {
        serialize_expr(self, symbol_table, expr_id)
    }

    /// Pretty-prints a `Statement` based on its `StmtId`
    /// with respect to the current `Transaction`
    pub fn format_stmt(&self, stmt_id: &StmtId, symbol_table: &SymbolTable) -> String {
        let mut buffer: Vec<u8> = vec![];
        let _ = build_statements(&mut buffer, self, symbol_table, stmt_id, 0);
        String::from_utf8(buffer).unwrap().trim_end().to_string()
    }

    // convenience clone accessors for constructing an IR from a Protocol AST
    pub fn exprs_clone(&self) -> PrimaryMap<ExprId, Expr> {
        self.ctx.exprs_clone()
    }

    pub fn dont_care_id(&self) -> ExprId {
        self.ctx.dont_care_id()
    }

    pub fn expr_loc_clone(&self) -> SecondaryMap<ExprId, (usize, usize, usize)> {
        self.ctx.expr_loc_clone()
    }
}

impl Deref for Protocol {
    type Target = ProtocolContext;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for Protocol {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

impl Index<ExprId> for ProtocolContext {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

impl Index<&ExprId> for ProtocolContext {
    type Output = Expr;

    fn index(&self, index: &ExprId) -> &Self::Output {
        &self.exprs[*index]
    }
}

impl Index<ExprId> for Protocol {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.ctx.exprs[index]
    }
}

impl Index<&ExprId> for Protocol {
    type Output = Expr;

    fn index(&self, index: &ExprId) -> &Self::Output {
        &self.ctx.exprs[*index]
    }
}

impl Index<StmtId> for Protocol {
    type Output = Stmt;

    fn index(&self, index: StmtId) -> &Self::Output {
        &self.stmts[index]
    }
}

impl Index<&StmtId> for Protocol {
    type Output = Stmt;

    fn index(&self, index: &StmtId) -> &Self::Output {
        &self.stmts[*index]
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StmtId(u32);
entity_impl!(StmtId, "stmt");

#[derive(Debug, Clone, Eq, PartialEq, Hash, strum_macros::EnumDiscriminants)]
#[strum_discriminants(derive(strum_macros::Display, strum_macros::EnumIter, Hash))]
#[strum_discriminants(strum(serialize_all = "snake_case"))]
pub enum Stmt {
    Block(Vec<StmtId>),
    Assign(SymbolId, ExprId),
    Step,
    Fork,
    While(ExprId, StmtId),
    /// Bounded loop with fixed no. of iterations
    /// (`ExprId` is the no. of iterations, `StmtId` is the loop body)
    RepeatLoop(ExprId, StmtId),
    ForInLoop(SymbolId, ExprId, StmtId),
    IfElse(ExprId, StmtId, StmtId),
    AssertEq(ExprId, ExprId),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct ExprId(u32);
entity_impl!(ExprId, "expr");

/// Enum representing a location in the IR that can be
/// either an expression or a statement.
/// (This is used in generic error-reporting functions that can
/// accept both `ExprId`s & `StmtId`s.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocationId {
    Expr(ExprId),
    Stmt(StmtId),
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BinOp {
    Equal,
    Concat,
    Add,
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
    /// Slice: args are msb first, then lsb
    Slice(ExprId, u32, u32),
    /// Inside a ForInLoop, this evaluates to true/false dending on what iteration we are on
    IsLastIteration,
    /// Inside a loop, this evaluates to the current number of _finished_ iterations.
    /// So in the first iteration, this evaluates to zero.
    IterCount(u32),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BoxedExpr {
    // (have start and end as usize in each variant)
    // nullary
    Const(BitVecValue, usize, usize),
    Sym(SymbolId, usize, usize),
    DontCare(usize, usize),
    IsLastIteration(usize, usize),
    IterCount(u32, usize, usize),
    // unary
    Binary(BinOp, Box<BoxedExpr>, Box<BoxedExpr>, usize, usize),
    // binary
    Unary(UnaryOp, Box<BoxedExpr>, usize, usize),
    // indexing
    Slice(Box<BoxedExpr>, u32, u32, usize, usize),
}

impl BoxedExpr {
    // starting character of the expression
    pub fn start(&self) -> usize {
        match self {
            BoxedExpr::Const(_, start, _) => *start,
            BoxedExpr::Sym(_, start, _) => *start,
            BoxedExpr::DontCare(start, _) => *start,
            BoxedExpr::IsLastIteration(start, _) => *start,
            BoxedExpr::IterCount(_, start, _) => *start,
            BoxedExpr::Binary(_, _, _, start, _) => *start,
            BoxedExpr::Unary(_, _, start, _) => *start,
            BoxedExpr::Slice(_, _, _, start, _) => *start,
        }
    }

    // ending character of the expression
    pub fn end(&self) -> usize {
        match self {
            BoxedExpr::Const(_, _, end) => *end,
            BoxedExpr::Sym(_, _, end) => *end,
            BoxedExpr::DontCare(_, end) => *end,
            BoxedExpr::IsLastIteration(_, end) => *end,
            BoxedExpr::IterCount(_, _, end) => *end,
            BoxedExpr::Binary(_, _, _, _, end) => *end,
            BoxedExpr::Unary(_, _, _, end) => *end,
            BoxedExpr::Slice(_, _, _, _, end) => *end,
        }
    }
}

pub fn find_symbols(ctx: &ProtocolContext, e: ExprId) -> FxHashSet<SymbolId> {
    let mut out = FxHashSet::default();
    let mut todo = vec![e];
    while let Some(e) = todo.pop() {
        match ctx[e].clone() {
            Expr::Const(_) => {}
            Expr::Sym(s) => {
                out.insert(s);
            }
            Expr::DontCare => {}
            Expr::Binary(_, a, b) => {
                todo.push(a);
                todo.push(b);
            }
            Expr::Unary(_, a) => {
                todo.push(a);
            }
            Expr::Slice(a, _, _) => {
                todo.push(a);
            }
            Expr::IsLastIteration => {}
            Expr::IterCount(_) => {}
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::symbol::{Arg, Dir, Field, SymbolKind};

    #[test]
    fn create_add_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 0) declare struct
        let mut symbols = SymbolTable::default();
        let add_struct = symbols.add_struct(
            "Adder".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("s".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        // 1) declare symbols that are local to the add protocol
        let add_scope = symbols.enter_scope("add");
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32), SymbolKind::Arg(0));
        let b: SymbolId =
            symbols.add_without_parent("b".to_string(), Type::BitVec(32), SymbolKind::Arg(1));
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(32), SymbolKind::Arg(2));
        assert_eq!(symbols["s"], symbols[s]);

        let dut = symbols.add_without_parent(
            "dut".to_string(),
            Type::Struct(add_struct),
            SymbolKind::Dut,
        );
        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        let dut_b = symbols.add_with_parent("b".to_string(), dut);
        let dut_s = symbols.add_with_parent("s".to_string(), dut);
        assert_eq!(symbols["dut.s"], symbols[dut_s]);
        assert_eq!(symbols["s"], symbols[s]);

        // Print the symbol table to demonstrate Display trait
        println!("\n{}", symbols);

        // 2) create transaction
        let mut add = Protocol::new("add".to_string(), add_scope);
        add.args = vec![Arg::new(a), Arg::new(b), Arg::new(s)];

        // 3) create expressions
        let a_expr = add.e(Expr::Sym(a));
        let b_expr = add.e(Expr::Sym(b));
        // let one_expr = add.e(Expr::Const(BitVecValue::from_u64(1, 1)));
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
        assert_eq!(add.used_constructs(), "assign, step, fork");
        symbols.exit_scope();
    }

    #[test]
    fn serialize_calyx_go_done_transaction() {
        // Manually create the expected result of parsing `calyx_go_done`.
        // Note that the order in which things are created will be different in the parser.

        // 0) declare struct
        let mut symbols = SymbolTable::default();
        let dut_struct = symbols.add_struct(
            "Calyx".to_string(),
            vec![
                Field::new("ii".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("go".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("done".to_string(), Dir::Out, Type::BitVec(32)),
                Field::new("oo".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        // 1) declare symbols local to the calyx_go_done protocol
        let scope = symbols.enter_scope("calyx_go_done");
        let ii = symbols.add_without_parent("ii".to_string(), Type::BitVec(32), SymbolKind::Arg(0));
        let oo = symbols.add_without_parent("oo".to_string(), Type::BitVec(32), SymbolKind::Arg(1));
        assert_eq!(symbols["oo"], symbols[oo]);
        let dut = symbols.add_without_parent(
            "dut".to_string(),
            Type::Struct(dut_struct),
            SymbolKind::Dut,
        );
        let dut_ii = symbols.add_with_parent("ii".to_string(), dut);
        let dut_go = symbols.add_with_parent("go".to_string(), dut);
        let dut_done = symbols.add_with_parent("done".to_string(), dut);
        let dut_oo = symbols.add_with_parent("oo".to_string(), dut);
        assert_eq!(symbols["dut.oo"], symbols[dut_oo]);
        assert_eq!(symbols["oo"], symbols[oo]);

        // 2) create transaction
        let mut calyx_go_done = Protocol::new("calyx_go_done".to_string(), scope);
        calyx_go_done.args = vec![Arg::new(ii), Arg::new(oo)];
        calyx_go_done.dut_sym = dut;

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        let cond_expr = calyx_go_done.e(Expr::Binary(BinOp::Equal, dut_done_expr, one_expr));
        let not_expr = calyx_go_done.e(Expr::Unary(UnaryOp::Not, cond_expr));

        // 4) create statements
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
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
        assert_eq!(calyx_go_done.used_constructs(), "assign, step, while");
        symbols.exit_scope();
    }
}
