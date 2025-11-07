// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use baa::BitVecValue;
use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};
use rustc_hash::FxHashMap;
use std::ops::Index;

use crate::serialize::{build_statements, serialize_expr, serialize_type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    /// The name of the `Transaction`
    pub name: String,

    /// List of `Arg`s to the `Transaction`
    pub args: Vec<Arg>,

    /// The body of the `Transaction`, identified by its `StmtId`
    pub body: StmtId,

    /// Optional type parameter (identified by its `SymbolId`)
    pub type_param: Option<SymbolId>,

    /// Maps `ExprId`s to their corresponding `Expr`s
    exprs: PrimaryMap<ExprId, Expr>,

    /// The distinguished `ExprId` corresponding to `DontCare`
    dont_care_id: ExprId,

    /// Maps `StmtId`s to their corresponding `Stmt`s
    stmts: PrimaryMap<StmtId, Stmt>,
    expr_loc: SecondaryMap<ExprId, (usize, usize, usize)>,
    stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)>,
}

impl Transaction {
    pub fn new(name: String) -> Self {
        let mut exprs = PrimaryMap::new();
        let dont_care_id = exprs.push(Expr::DontCare);
        let mut stmts = PrimaryMap::new();
        let block_id: StmtId = stmts.push(Stmt::Block(vec![]));
        let expr_loc: SecondaryMap<ExprId, (usize, usize, usize)> = SecondaryMap::new();
        let stmt_loc: SecondaryMap<StmtId, (usize, usize, usize)> = SecondaryMap::new();
        Self {
            name,
            args: Vec::default(),
            body: block_id,
            type_param: None, // guranteed to become Some after parsing by grammar constraints
            exprs,
            dont_care_id,
            stmts,
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

    pub fn next_stmt_mapping(&self) -> FxHashMap<StmtId, Option<StmtId>> {
        self.next_stmt_mapping_helper(self.body, None)
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
                    Stmt::While(_, body_id) => {
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
            let symbol_id = arg.symbol;
            let symbol_table_entry = &symbol_table[symbol_id];
            arg_types.push(symbol_table_entry.tpe)
        }
        arg_types
    }

    /// Retrieves the `SymbolId`s of all the output parameters of a transaction,
    /// returning an `Iterator`
    pub fn get_output_param_symbols(&self) -> impl Iterator<Item = SymbolId> {
        self.args.iter().filter_map(|arg| {
            if arg.dir == Dir::Out {
                Some(arg.symbol)
            } else {
                None
            }
        })
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
    /// Checks whether two types are *equivalent*,
    /// i.e. if two bit-vector types have the same length,
    /// or if two `struct`s have the same `StructId`.
    /// NB: this function returns `false` if either type is `Unknown`,
    /// or if any of the aforementioned cases don't hold.
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
    Concat,
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
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BoxedExpr {
    // (have start and end as usize in each variant)
    // nullary
    Const(BitVecValue, usize, usize),
    Sym(SymbolId, usize, usize),
    DontCare(usize, usize),
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
            BoxedExpr::Binary(_, _, _, _, end) => *end,
            BoxedExpr::Unary(_, _, _, end) => *end,
            BoxedExpr::Slice(_, _, _, _, end) => *end,
        }
    }
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

    /// Retrieves the (fully-qualified) names of all the output pins of a `Struct`,
    /// returning an `Iterator` of `String`s
    pub fn get_output_pin_names(&self) -> impl Iterator<Item = String> {
        self.pins.iter().filter_map(|field| {
            if field.dir == Dir::Out {
                Some(format!("{}.{}", self.name, field.name))
            } else {
                None
            }
        })
    }
}

/// Datatype representing a `Field` in a `Struct`, contains:
/// - The name of the field
/// - The direction (`In` or `Out`)
/// - The `Type` of the field
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
        self.tpe
    }

    /// Computes the bitwidth of a `Field`. Note: this function panics
    /// if the `Type` of a `Field` is *not* a `BitVec`.
    pub fn bitwidth(&self) -> u32 {
        match self.tpe {
            Type::BitVec(width) => width,
            Type::Struct(_) => panic!("Unable to compute bitwidth for a struct type"),
            Type::Unknown => panic!("Unable to compute bitwidth for Type::Unknown"),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SymbolId(u32);
entity_impl!(SymbolId, "symbol");

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct SymbolTable {
    entries: PrimaryMap<SymbolId, SymbolTableEntry>,
    by_name_sym: FxHashMap<String, SymbolId>,
    structs: PrimaryMap<StructId, Struct>,
    by_name_struct: FxHashMap<String, StructId>,
}

/// Pretty-printer for `SymbolTable`s
impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "SymbolTable {{")?;

        // Display symbol table entries
        writeln!(f, "  Symbols:")?;
        for (symbol_id, entry) in self.entries.iter() {
            let type_str = serialize_type(self, entry.tpe());

            let parent_str = match entry.parent {
                Some(parent_id) => format!(
                    " [parent: symbol{} \"{}\"]",
                    parent_id.0, self[parent_id].name
                ),
                None => "".to_string(),
            };

            writeln!(
                f,
                "    symbol{} \"{}\": {}{}",
                symbol_id.0,
                entry.full_name(self),
                type_str,
                parent_str
            )?;
        }

        // Display structs
        if !self.structs.is_empty() {
            writeln!(f)?;
            writeln!(f, "  Structs:")?;
            for (struct_id, struct_def) in self.structs.iter() {
                writeln!(f, "    struct{} \"{}\" {{", struct_id.0, struct_def.name)?;
                for field in &struct_def.pins {
                    let type_str = serialize_type(self, field.tpe());
                    writeln!(f, "      {} {}: {}", field.dir, field.name, type_str)?;
                }
                writeln!(f, "    }}")?;
            }
        }

        write!(f, "}}")
    }
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
        };
        let lookup_name = entry.full_name(self);

        assert!(
            !self.by_name_sym.contains_key(&lookup_name),
            "we already have an entry for {lookup_name}!",
        );

        let id = self.entries.push(entry);
        self.by_name_sym.insert(lookup_name, id);
        id
    }

    /// Takes a string and returns the corresponding `SymbolId` (if one exists)
    pub fn symbol_id_from_name(&self, name: &str) -> Option<SymbolId> {
        self.by_name_sym.get(name).copied()
    }

    /// Takes a `SymbolId` and returns the corresponding (qualified) full name
    pub fn full_name_from_symbol_id(&self, symbol_id: &SymbolId) -> String {
        self[symbol_id].full_name(self)
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
        };
        let lookup_name = entry.full_name(self);

        assert!(
            !self.by_name_sym.contains_key(&lookup_name),
            "we already have an entry for {lookup_name}!",
        );

        let id = self.entries.push(entry);
        self.by_name_sym.insert(lookup_name, id);
        id
    }

    pub fn add_struct(&mut self, name: String, pins: Vec<Field>) -> StructId {
        let s = Struct {
            name: name.to_string(),
            pins,
        };
        let id = self.structs.push(s);

        self.by_name_struct.insert(name, id);
        id
    }

    pub fn struct_id_from_name(&mut self, name: &str) -> Option<StructId> {
        self.by_name_struct.get(name).copied()
    }

    pub fn struct_ids(&self) -> Vec<StructId> {
        self.structs.keys().collect()
    }

    pub fn get_children(&self, parent_name: &SymbolId) -> Vec<SymbolId> {
        let mut children = vec![];
        for (id, entry) in self.entries.iter() {
            if entry.parent() == Some(*parent_name) {
                children.push(id);
            }
        }
        children
    }
}

impl Index<&str> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &str) -> &Self::Output {
        let index = self.by_name_sym[index];
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
    /// Used to compute the fully qualified name.
    parent: Option<SymbolId>,
}

impl SymbolTableEntry {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn tpe(&self) -> Type {
        self.tpe
    }

    /// Retrieves the `SymbolID` of the parent symbol
    /// (e.g. if the current entry refers to the field of a struct,
    /// then this method returns the parent struct)
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

        // Print the symbol table to demonstrate Display trait
        println!("\n{}", symbols);

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
        calyx_go_done.type_param = Some(dut);

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
    }
}
