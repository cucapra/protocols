// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::{BinOp, Expr as AstExpr, ExprId, ProtocolContext};
use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use baa::BitVecValue;
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use patronus::expr::{Context, ExprRef, Type as PatronusType};
use rustc_hash::FxHashMap;
use std::ops::{Deref, DerefMut, Index};

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct NodeId(u32);
entity_impl!(NodeId, "node");

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
// ops (so far) are non-recrusive, may not be necessary to have an ID, but useful for debug maps
// if we want debug info on expressions and transitions, we'll need a way to do this with or without Ids
pub struct OpId(u32);
entity_impl!(OpId, "op");

#[derive(Debug, Clone, PartialEq, Eq)]
/// an Action is a guard and an operation to perform when the guard is true
pub struct Action {
    pub guard: ExprRef,
    pub op: OpId,
}

impl Action {
    pub fn new(guard: ExprRef, op: OpId) -> Self {
        Self { guard, op }
    }

    /// use the new guard instead of the old one
    pub fn with_guard(&self, guard: ExprRef) -> Self {
        Self { guard, op: self.op }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A Transition is a guard, a target node, and flag if this transition consumes step
pub struct Transition {
    pub guard: ExprRef,
    pub target: NodeId,
    pub consumes_step: bool,
}

impl Transition {
    pub fn new(guard: ExprRef, target: NodeId, consumes_step: bool) -> Self {
        Self {
            guard,
            target,
            consumes_step,
        }
    }

    /// use the new guard instead of the old one
    pub fn with_guard(&self, guard: ExprRef) -> Self {
        Self {
            guard,
            target: self.target,
            consumes_step: self.consumes_step,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
// A node is a (logically) unorded set of actions and transitions
pub struct Node {
    pub actions: Vec<Action>,
    pub transitions: Vec<Transition>,
}

impl Node {
    pub fn empty() -> Self {
        Self {
            actions: vec![],
            transitions: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Assign(SymbolId, ExprRef),
    AssertEq(ExprRef, ExprRef),
    Fork,
    Done,
}

#[derive(Clone)]
pub struct ProtoGraph {
    pub protoCtx: ProtocolContext,

    /// The entrypoint of the `Protocol`
    pub entry: NodeId,

    /// Patronus expression context
    pub exprCtx : Context,

    /// Maps AST `ExprId`s to the Patronus `ExprRef`s created during lowering.
    ast_to_pat_expr: FxHashMap<ExprId, ExprRef>,

    /// Reverse map for consumers that still want to evaluate/pretty-print through the AST.
    pat_to_ast_expr: FxHashMap<ExprRef, ExprId>,

    /// Cached Patronus expressions for AST `DontCare` nodes, keyed by type.
    dont_care_exprs: FxHashMap<PatronusType, ExprRef>,

    /// Cached Patronus symbol expressions, keyed by frontend `SymbolId`.
    symbol_exprs: FxHashMap<SymbolId, ExprRef>,

    /// Maps `NodeId`s to their corresponding `Node`s
    nodes: PrimaryMap<NodeId, Node>,

    /// Maps `OpId`s to their corresponding `Op`s
    ops: PrimaryMap<OpId, Op>,

    op_loc: SecondaryMap<OpId, (usize, usize, usize)>,
}

impl ProtoGraph {
    pub fn new(mut protoCtx: ProtocolContext) -> Self {
        let exprCtx = Context::default();

        // Keep explicit AST mirrors for the cached Patronus constants so legacy consumers
        // can still translate a lowered expression back to an AST expression id.
        let true_ast = protoCtx.e(AstExpr::Const(BitVecValue::from_u64(1, 1)));
        let false_ast = protoCtx.e(AstExpr::Const(BitVecValue::from_u64(0, 1)));

        let true_pat = exprCtx.get_true();
        let false_pat = exprCtx.get_false();

        let mut ast_to_pat_expr = FxHashMap::default();
        let mut pat_to_ast_expr = FxHashMap::default();
        ast_to_pat_expr.insert(true_ast, true_pat);
        ast_to_pat_expr.insert(false_ast, false_pat);
        pat_to_ast_expr.insert(true_pat, true_ast);
        pat_to_ast_expr.insert(false_pat, false_ast);

        let mut nodes = PrimaryMap::new();
        let entry = Node::empty();
        let entry_id: NodeId = nodes.push(entry);

        let ops = PrimaryMap::new();
        let op_loc: SecondaryMap<OpId, (usize, usize, usize)> = SecondaryMap::new();

        Self {
            protoCtx,
            entry: entry_id,
            exprCtx,
            ast_to_pat_expr,
            pat_to_ast_expr,
            dont_care_exprs: FxHashMap::default(),
            symbol_exprs: FxHashMap::default(),
            nodes,
            ops,
            op_loc,
        }
    }

    pub fn true_id(&self) -> ExprRef {
        self.exprCtx.get_true()
    }

    pub fn false_id(&self) -> ExprRef {
        self.exprCtx.get_false()
    }

    pub fn expr_for_ast(&self, expr_id: ExprId) -> Option<ExprRef> {
        self.ast_to_pat_expr.get(&expr_id).copied()
    }

    pub fn ast_expr_for(&self, expr_ref: ExprRef) -> Option<ExprId> {
        self.pat_to_ast_expr.get(&expr_ref).copied()
    }

    pub fn record_expr_mapping(&mut self, ast_expr: ExprId, pat_expr: ExprRef) {
        self.ast_to_pat_expr.insert(ast_expr, pat_expr);
        self.pat_to_ast_expr.insert(pat_expr, ast_expr);
    }

    pub fn dont_care_expr(&mut self, tpe: PatronusType) -> ExprRef {
        if let Some(expr) = self.dont_care_exprs.get(&tpe) {
            return *expr;
        }

        let expr = match tpe {
            PatronusType::BV(width) => {
                let name = format!("__dontcare_bv_{width}_{}", self.dont_care_exprs.len());
                self.exprCtx.bv_symbol(&name, width)
            }
            PatronusType::Array(array_tpe) => {
                let name = format!(
                    "__dontcare_arr_{}_{}x{}",
                    self.dont_care_exprs.len(),
                    array_tpe.index_width,
                    array_tpe.data_width
                );
                self.exprCtx
                    .array_symbol(&name, array_tpe.index_width, array_tpe.data_width)
            }
        };

        self.dont_care_exprs.insert(tpe, expr);
        expr
    }

    pub fn symbol_expr(&mut self, symbol_id: SymbolId, symbols: &SymbolTable) -> ExprRef {
        if let Some(expr) = self.symbol_exprs.get(&symbol_id) {
            return *expr;
        }

        let entry = &symbols[symbol_id];
        let full_name = entry.full_name(symbols);
        let expr = match entry.tpe() {
            FrontType::BitVec(width) => self.exprCtx.bv_symbol(&full_name, width),
            FrontType::Struct(_) | FrontType::Seq(_) | FrontType::UnsignedInt | FrontType::Unknown => {
                panic!(
                    "unsupported symbol type {} for {}",
                    crate::frontend::serialize::serialize_type(symbols, entry.tpe()),
                    full_name
                )
            }
        };
        self.symbol_exprs.insert(symbol_id, expr);
        expr
    }

    pub fn lower_and(&mut self, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        let ast_lhs = self
            .ast_expr_for(lhs)
            .expect("missing AST mapping for left-hand side of lowered AND");
        let ast_rhs = self
            .ast_expr_for(rhs)
            .expect("missing AST mapping for right-hand side of lowered AND");
        let ast_expr = self.protoCtx.e(AstExpr::Binary(BinOp::And, ast_lhs, ast_rhs));
        let pat_expr = self.exprCtx.and(lhs, rhs);
        self.record_expr_mapping(ast_expr, pat_expr);
        pat_expr
    }

    pub fn lower_symbol(&mut self, symbol_id: SymbolId, symbols: &SymbolTable) -> ExprRef {
        self.symbol_expr(symbol_id, symbols)
    }

    pub fn make_ast_expr(&mut self, expr: AstExpr) -> ExprId {
        self.protoCtx.e(expr)
    }

    /// Returns the Patronus expression type corresponding to an AST symbol type.
    pub fn ast_to_patronus_type(tpe: FrontType) -> PatronusType {
        match tpe {
            FrontType::BitVec(width) => PatronusType::BV(width),
            FrontType::Struct(_) | FrontType::Seq(_) | FrontType::UnsignedInt | FrontType::Unknown => {
                panic!("unsupported frontend type for Patronus lowering: {:?}", tpe)
            }
        }
    }

    /// add a new node to the IR
    pub fn n(&mut self, node: Node) -> NodeId {
        self.nodes.push(node)
    }

    /// get the next node id (so we can build transitions to it)
    pub fn next_node_id(&self) -> NodeId {
        self.nodes.next_key()
    }

    /// add a new op to the IR
    pub fn o(&mut self, op: Op) -> OpId {
        self.ops.push(op)
    }

    pub fn nodes(&self) -> impl Iterator<Item = (NodeId, &Node)> + '_ {
        self.nodes.iter()
    }

    pub(crate) fn node_mut(&mut self, node_id: NodeId) -> &mut Node {
        &mut self.nodes[node_id]
    }

    /// push an action `a` onto `node_id`
    pub fn push_action(&mut self, node_id: NodeId, a: Action) {
        self.nodes[node_id].actions.push(a);
    }

    /// push a transition `t` onto `node_id`
    pub fn push_transition(&mut self, node_id: NodeId, t: Transition) {
        self.nodes[node_id].transitions.push(t);
    }
}

impl Deref for ProtoGraph {
    type Target = ProtocolContext;

    fn deref(&self) -> &Self::Target {
        &self.protoCtx
    }
}

impl DerefMut for ProtoGraph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.protoCtx
    }
}

impl Index<ExprRef> for ProtoGraph {
    type Output = AstExpr;

    fn index(&self, index: ExprRef) -> &Self::Output {
        let ast_expr = self
            .ast_expr_for(index)
            .unwrap_or_else(|| panic!("missing AST mapping for {index:?}"));
        &self.protoCtx[ast_expr]
    }
}

impl Index<usize> for Node {
    type Output = Transition;

    fn index(&self, index: usize) -> &Self::Output {
        &self.transitions[index]
    }
}

impl Index<&ExprRef> for ProtoGraph {
    type Output = AstExpr;

    fn index(&self, index: &ExprRef) -> &Self::Output {
        let ast_expr = self
            .ast_expr_for(*index)
            .unwrap_or_else(|| panic!("missing AST mapping for {index:?}"));
        &self.protoCtx[ast_expr]
    }
}

impl Index<NodeId> for ProtoGraph {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index]
    }
}

impl Index<&NodeId> for ProtoGraph {
    type Output = Node;

    fn index(&self, index: &NodeId) -> &Self::Output {
        &self.nodes[*index]
    }
}

impl Index<OpId> for ProtoGraph {
    type Output = Op;

    fn index(&self, index: OpId) -> &Self::Output {
        &self.ops[index]
    }
}

impl Index<&OpId> for ProtoGraph {
    type Output = Op;

    fn index(&self, index: &OpId) -> &Self::Output {
        &self.ops[*index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::parser::parse_file;
    use crate::ir::lowering::lower_ast_to_ir;
    use std::path::Path;
    use tempfile::NamedTempFile;

    fn parse_and_lower(source: &str) -> ProtoGraph {
        let file = NamedTempFile::new().unwrap();
        std::fs::write(file.path(), source).unwrap();

        parse_and_lower_file(file.path(), None)
    }

    fn parse_and_lower_file(path: impl AsRef<Path>, protocol_name: Option<&str>) -> ProtoGraph {
        let mut handler = DiagnosticHandler::default();
        let parsed = parse_file(path, &mut handler).unwrap();
        let (ast, symbol_table) = match protocol_name {
            Some(protocol_name) => parsed
                .into_iter()
                .find(|(ast, _)| ast.name == protocol_name)
                .unwrap(),
            None => {
                assert_eq!(parsed.len(), 1);
                parsed.into_iter().next().unwrap()
            }
        };
        lower_ast_to_ir(ast, &symbol_table)
    }

    #[test]
    fn lowers_straight_line_protocol_into_distinct_ir_nodes() {
        let ir = parse_and_lower(
            r#"
            struct Dummy {
              in a: u32,
              out b: u32,
            }

            prot pipe<dut: Dummy>(a: u32, b: u32) {
              dut.a := a;
              step();
              assert_eq(b, dut.b);
            }
            "#,
        );

        assert_eq!(ir.name, "pipe");
        assert_eq!(ir.args.len(), 2);
        assert_eq!(ir.nodes.len(), 5);
        assert_eq!(ir.ops.len(), 3);

        let entry = &ir.nodes[ir.entry];
        assert!(entry.actions.is_empty());
        assert_eq!(entry.transitions.len(), 1);
        assert_eq!(
            entry.transitions[0],
            Transition {
                guard: ir.true_id(),
                target: NodeId(4),
                consumes_step: false,
            }
        );

        let assign = &ir.nodes[NodeId(4)];
        assert_eq!(assign.actions.len(), 1);
        assert_eq!(assign.actions[0].guard, ir.true_id());
        assert!(matches!(ir.ops[assign.actions[0].op], Op::Assign(_, _)));
        assert_eq!(
            assign.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(3),
                consumes_step: false,
            }]
        );

        let step = &ir.nodes[NodeId(3)];
        assert!(step.actions.is_empty());
        assert_eq!(
            step.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(2),
                consumes_step: true,
            }]
        );

        let assert_node = &ir.nodes[NodeId(2)];
        assert_eq!(assert_node.actions.len(), 1);
        assert_eq!(assert_node.actions[0].guard, ir.true_id());
        assert!(matches!(
            ir.ops[assert_node.actions[0].op],
            Op::AssertEq(_, _)
        ));
        assert_eq!(
            assert_node.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(1),
                consumes_step: false,
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 1);
        assert_eq!(exit.actions[0].guard, ir.true_id());
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(exit.transitions.is_empty());
    }

    #[test]
    fn lowers_fork_into_action_and_non_step_transition() {
        let ir = parse_and_lower(
            r#"
            struct Dummy {
              in a: u32,
              out b: u32,
            }

            prot pipe<dut: Dummy>(a: u32, b: u32) {
              fork();
            }
            "#,
        );

        assert_eq!(ir.nodes.len(), 3);
        assert_eq!(ir.ops.len(), 2);

        let fork = &ir.nodes[NodeId(2)];
        assert_eq!(fork.actions.len(), 1);
        assert!(matches!(ir.ops[fork.actions[0].op], Op::Fork));
        assert_eq!(
            fork.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(1),
                consumes_step: false,
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 1);
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(exit.transitions.is_empty());
    }

    #[test]
    fn lowers_add_d1_fixture_via_parser_and_lowering() {
        let ir = parse_and_lower_file("tests/adders/adder_d1/add_d1.prot", Some("add"));

        assert_eq!(ir.name, "add");
        assert_eq!(ir.args.len(), 3);
        assert_eq!(ir.nodes.len(), 10);
        assert_eq!(ir.ops.len(), 7);

        let entry = &ir.nodes[ir.entry];
        assert!(entry.actions.is_empty());
        assert_eq!(
            entry.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(9),
                consumes_step: false,
            }]
        );

        let step = &ir.nodes[NodeId(7)];
        assert!(step.actions.is_empty());
        assert_eq!(
            step.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(6),
                consumes_step: true,
            }]
        );

        let fork = &ir.nodes[NodeId(3)];
        assert_eq!(fork.actions.len(), 1);
        assert!(matches!(ir.ops[fork.actions[0].op], Op::Fork));
        assert_eq!(
            fork.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(2),
                consumes_step: false,
            }]
        );

        let last_step = &ir.nodes[NodeId(2)];
        assert!(last_step.actions.is_empty());
        assert_eq!(
            last_step.transitions,
            vec![Transition {
                guard: ir.true_id(),
                target: NodeId(1),
                consumes_step: true,
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 1);
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(exit.transitions.is_empty());
    }
}
