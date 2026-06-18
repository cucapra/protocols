// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::ProtocolContext;
use crate::frontend::symbol::SymbolId;
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use patronus::expr::{Context as ExprContext, ExprRef, Simplifier, SparseExprMap};
use rustc_hash::FxHashMap;
use std::ops::{Deref, DerefMut, Index};

pub const DONTCARE_PREFIX: &str = "__dontcare__";

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
    InternalAssertFalse,
    Done,
}

pub struct ProtoGraph {
    pub proto_ctx: ProtocolContext,

    /// The entrypoint of the `Protocol`
    pub entry: NodeId,

    /// Patronus expression context
    pub expr_ctx: ExprContext,

    /// Patronus simplifier
    pub simplifier: Simplifier<SparseExprMap<Option<ExprRef>>>,

    /// Cached Patronus symbol expressions, keyed by frontend `SymbolId`.
    symbol_expr: FxHashMap<SymbolId, ExprRef>,

    nodes: PrimaryMap<NodeId, Node>,

    ops: PrimaryMap<OpId, Op>,

    #[allow(dead_code)]
    op_loc: SecondaryMap<OpId, (usize, usize, usize)>,
}

impl Clone for ProtoGraph {
    fn clone(&self) -> Self {
        Self {
            proto_ctx: self.proto_ctx.clone(),
            entry: self.entry,
            expr_ctx: self.expr_ctx.clone(),
            // we can just make a fresh simplifier
            simplifier: Simplifier::new(SparseExprMap::default()),
            symbol_expr: self.symbol_expr.clone(),
            nodes: self.nodes.clone(),
            ops: self.ops.clone(),
            op_loc: self.op_loc.clone(),
        }
    }
}

impl ProtoGraph {
    pub fn new(proto_ctx: ProtocolContext) -> Self {
        let expr_ctx = ExprContext::default();
        let mut nodes = PrimaryMap::new();
        let entry = Node::empty();
        let entry_id: NodeId = nodes.push(entry);

        let ops = PrimaryMap::new();
        let op_loc: SecondaryMap<OpId, (usize, usize, usize)> = SecondaryMap::new();

        Self {
            proto_ctx,
            entry: entry_id,
            expr_ctx,
            simplifier: Simplifier::new(SparseExprMap::default()),
            symbol_expr: FxHashMap::default(),
            nodes,
            ops,
            op_loc,
        }
    }

    pub fn true_id(&self) -> ExprRef {
        self.expr_ctx.get_true()
    }

    pub fn false_id(&self) -> ExprRef {
        self.expr_ctx.get_false()
    }

    pub fn symbol_expr(&self, symbol_id: SymbolId) -> Option<ExprRef> {
        self.symbol_expr.get(&symbol_id).copied()
    }

    pub fn cache_symbol_expr(&mut self, symbol_id: SymbolId, expr: ExprRef) {
        self.symbol_expr.insert(symbol_id, expr);
    }

    /// convenience methods for construction simplified
    /// (p AND q) or (p OR q) expressions
    pub fn and_guard(&mut self, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        let expr = self.expr_ctx.and(lhs, rhs);
        self.simplifier.simplify(&mut self.expr_ctx, expr)
    }

    pub fn or_guard(&mut self, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        let expr = self.expr_ctx.or(lhs, rhs);
        self.simplifier.simplify(&mut self.expr_ctx, expr)
    }

    // TODO: add a verify simplifications helper

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
        &self.proto_ctx
    }
}

impl DerefMut for ProtoGraph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.proto_ctx
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
        let (symbol_table, protocols) = parse_file(path, &mut handler).unwrap();
        let ast = match protocol_name {
            Some(protocol_name) => protocols
                .into_iter()
                .find(|ast| ast.name == protocol_name)
                .unwrap(),
            None => {
                assert_eq!(protocols.len(), 1);
                protocols.into_iter().next().unwrap()
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
