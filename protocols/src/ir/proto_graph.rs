// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::*;
use crate::frontend::symbol::SymbolId;
use baa::BitVecValue;
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use std::ops::{Deref, DerefMut, Index};

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
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
    pub guard: ExprId,
    pub op: OpId,
}

impl Action {
    pub fn new(guard: ExprId, op: OpId) -> Self {
        Self { guard, op }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A Transition is a guard, a target node, and flag if this transition consumes step
pub struct Transition {
    pub guard: ExprId,
    pub target: NodeId,
    pub consumes_step: bool,
}

impl Transition {
    pub fn new(guard: ExprId, target: NodeId, consumes_step: bool) -> Self {
        Self {
            guard,
            target,
            consumes_step,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
// A node is a (logically) unorded set of actions and transitions
pub struct Node {
    actions: Vec<Action>,
    transitions: Vec<Transition>,
}

impl Node {
    pub fn empty() -> Self {
        Self {
            actions: vec![],
            transitions: vec![],
        }
    }

    pub fn action_iter(&self) -> impl Iterator<Item = &Action> {
        self.actions.iter()
    }

    pub fn transition_iter(&self) -> impl Iterator<Item = &Transition> {
        self.transitions.iter()
    }

    pub(crate) fn actions_mut(&mut self) -> &mut Vec<Action> {
        &mut self.actions
    }

    pub(crate) fn transitions_mut(&mut self) -> &mut Vec<Transition> {
        &mut self.transitions
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Assign(SymbolId, ExprId),
    AssertEq(ExprId, ExprId),
    Fork,
    Done,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtoGraph {
    pub ctx: ProtocolContext,

    /// The entrypoint of the `Protocol`
    pub entry: NodeId,

    /// Other distinguished expressions convenient in lowering
    true_id: ExprId,

    /// Maps `NodeId`s to their corresponding `Node`s
    nodes: PrimaryMap<NodeId, Node>,

    /// Maps `OpId`s to their corresponding `Op`s
    ops: PrimaryMap<OpId, Op>,

    op_loc: SecondaryMap<OpId, (usize, usize, usize)>,
}

impl ProtoGraph {
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

    /// get the convenience expressions
    pub fn true_id(&self) -> ExprId {
        self.true_id
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

    // reuse stuff from the AST
    pub fn new(mut ctx: ProtocolContext) -> Self {
        // set the convenience values for lowering
        // TODO: maybe some expressions are so common they need a canonical map from Expr -> ExprId
        let true_id = ctx.e(Expr::Const(BitVecValue::from_u64(1, 1)));

        // set up the empty entry node that always transitions to the next key
        let mut nodes = PrimaryMap::new();
        let entry = Node::empty();
        let entry_id: NodeId = nodes.push(entry);

        // set up empty ops map
        let ops = PrimaryMap::new();

        // set up op_loc with optionals (reuse existing expr_loc)
        let op_loc: SecondaryMap<OpId, (usize, usize, usize)> = SecondaryMap::new();

        Self {
            ctx,
            entry: entry_id,
            true_id,
            nodes: nodes.clone(),
            ops,
            op_loc,
        }
    }
}

impl Deref for ProtoGraph {
    type Target = ProtocolContext;

    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for ProtoGraph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

impl Index<ExprId> for ProtoGraph {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.ctx[index]
    }
}

impl Index<&ExprId> for ProtoGraph {
    type Output = Expr;

    fn index(&self, index: &ExprId) -> &Self::Output {
        &self.ctx[index]
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
        let (ast, _symbol_table) = match protocol_name {
            Some(protocol_name) => parsed
                .into_iter()
                .find(|(ast, _)| ast.name == protocol_name)
                .unwrap(),
            None => {
                assert_eq!(parsed.len(), 1);
                parsed.into_iter().next().unwrap()
            }
        };
        lower_ast_to_ir(ast)
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
