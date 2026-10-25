// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::ProtocolContext;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type};
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use patronus::expr::{
    Context, ExprRef, Simplifier, SparseExprMap, TypeCheck, simple_transform_expr,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::ops::{Deref, DerefMut, Index};

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct NodeId(u32);
entity_impl!(NodeId, "node");

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
// ops (so far) are non-recursive, may not be necessary to have an ID, but useful for debug maps
// if we want debug info on expressions and transitions, we'll need a way to do this with or without Ids
pub struct OpId(u32);
entity_impl!(OpId, "op");

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct LoopId(u32);
entity_impl!(LoopId, "l");

/// How a single invocation supplies the loop's finite sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopSource {
    /// Sequence argument supplying items; absent when the items are unused.
    pub argument: Option<SymbolId>,
    /// Exact source length, if supplied independently of the items.
    pub length: Option<ExprRef>,
    pub min_len: u64,
}

/// The three current FIFO inputs, separate from registers loaded from them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loop {
    pub source: LoopSource,
    pub data: ExprRef,
    pub last: ExprRef,
    pub valid: ExprRef,
}

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
pub struct TransitionRotation {
    pub protocol: String,
    pub amount: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A Transition is a guard, a target node, and flag if this transition consumes step
pub struct Transition {
    pub guard: ExprRef,
    pub target: NodeId,
    pub consumes_step: bool,
    pub rotations: Vec<TransitionRotation>,
}

impl Transition {
    pub fn new(guard: ExprRef, target: NodeId, consumes_step: bool) -> Self {
        Self {
            guard,
            target,
            consumes_step,
            rotations: Vec::new(),
        }
    }

    /// use the new guard instead of the old one
    pub fn with_guard(&self, guard: ExprRef) -> Self {
        Self {
            guard,
            target: self.target,
            consumes_step: self.consumes_step,
            rotations: self.rotations.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
// In contracted nodes, RHSs and consumers read incoming state and current
// inputs. State updates commit simultaneously; action order is already encoded
// in the expressions by contraction. Raw nodes place assignments before consumers.
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
pub struct Assignment {
    pub dont_care: ExprRef,
    pub concretes: Vec<(ExprRef, ExprRef)>,
}

impl Assignment {
    /// X wins, then the first applicable concrete alternative, otherwise hold.
    pub fn to_expr(&self, ctx: &mut Context, dont_care: ExprRef, default: ExprRef) -> ExprRef {
        let mut value = default;
        for &(guard, rhs) in self.concretes.iter().rev() {
            value = ctx.ite(guard, rhs, value);
        }
        if self.dont_care == ctx.get_false() {
            value
        } else {
            ctx.ite(self.dont_care, dont_care, value)
        }
    }

    pub fn concrete(false_id: ExprRef, guard: ExprRef, rhs: ExprRef) -> Self {
        Self {
            dont_care: false_id,
            concretes: vec![(guard, rhs)],
        }
    }

    pub fn dont_care(guard: ExprRef) -> Self {
        Self {
            dont_care: guard,
            concretes: vec![],
        }
    }

    pub fn from_rhs(false_id: ExprRef, guard: ExprRef, rhs: ExprRef, is_dont_care: bool) -> Self {
        if is_dont_care {
            Self {
                dont_care: guard,
                concretes: vec![],
            }
        } else {
            Self {
                dont_care: false_id,
                concretes: vec![(guard, rhs)],
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Assign(SymbolId, Assignment),
    AssertEq(ExprRef, ExprRef),
    /// Load a FIFO head signal into an ordinary automaton register. All three
    /// reads describe the same item and do not themselves advance the FIFO.
    Data {
        loop_id: LoopId,
        target: SymbolId,
    },
    Last {
        loop_id: LoopId,
        target: SymbolId,
    },
    Valid {
        loop_id: LoopId,
        target: SymbolId,
    },
    Fork,
    InternalAssertFalse,
    Done,
}

/// Substitute expression references when copying a transaction instance.
pub fn remap_expr(
    ctx: &mut Context,
    expr: ExprRef,
    substitutions: &FxHashMap<ExprRef, ExprRef>,
) -> ExprRef {
    simple_transform_expr(ctx, expr, |_, original, _| {
        substitutions.get(&original).copied()
    })
}

impl Op {
    /// View ordinary assignments and FIFO loads through the same state-update API.
    pub fn assignment(&self, ctx: &Context, graph: &ProtoGraph) -> Option<(SymbolId, Assignment)> {
        let (target, value) = match self {
            Self::Assign(target, assignment) => return Some((*target, assignment.clone())),
            Self::Data { loop_id, target } => (*target, graph.loops[*loop_id].data),
            Self::Last { loop_id, target } => (*target, graph.loops[*loop_id].last),
            Self::Valid { loop_id, target } => (*target, graph.loops[*loop_id].valid),
            _ => return None,
        };
        Some((
            target,
            Assignment::concrete(ctx.get_false(), ctx.get_true(), value),
        ))
    }

    /// Remap assignment targets together with every expression that reads them.
    pub fn remap(
        &self,
        ctx: &mut Context,
        substitutions: &FxHashMap<ExprRef, ExprRef>,
        targets: &FxHashMap<SymbolId, SymbolId>,
    ) -> Self {
        match self {
            Self::Assign(symbol, assignment) => Self::Assign(
                targets.get(symbol).copied().unwrap_or(*symbol),
                Assignment {
                    dont_care: remap_expr(ctx, assignment.dont_care, substitutions),
                    concretes: assignment
                        .concretes
                        .iter()
                        .map(|&(guard, rhs)| {
                            (
                                remap_expr(ctx, guard, substitutions),
                                remap_expr(ctx, rhs, substitutions),
                            )
                        })
                        .collect(),
                },
            ),
            Self::AssertEq(lhs, rhs) => {
                let lhs = remap_expr(ctx, *lhs, substitutions);
                let rhs = remap_expr(ctx, *rhs, substitutions);
                debug_assert_eq!(lhs.get_type(ctx), rhs.get_type(ctx));
                Self::AssertEq(lhs, rhs)
            }
            Self::Data { loop_id, target } => Self::Data {
                loop_id: *loop_id,
                target: targets.get(target).copied().unwrap_or(*target),
            },
            Self::Last { loop_id, target } => Self::Last {
                loop_id: *loop_id,
                target: targets.get(target).copied().unwrap_or(*target),
            },
            Self::Valid { loop_id, target } => Self::Valid {
                loop_id: *loop_id,
                target: targets.get(target).copied().unwrap_or(*target),
            },
            other => other.clone(),
        }
    }
}

pub struct ProtoGraph {
    // TODO: the ProtocolContext of a ProtoGraph is not really meaningful for a full concrete trace or a symbolic multi-protocol graph, so we may need to change this at some point
    pub proto_ctx: ProtocolContext,

    /// The entrypoint of the `Protocol`
    pub entry: NodeId,

    /// Patronus simplifier
    pub simplifier: Simplifier<SparseExprMap<Option<ExprRef>>>,

    /// Cached Patronus symbol expressions, keyed by frontend `SymbolId`.
    pub symbol_expr: FxHashMap<SymbolId, ExprRef>,

    /// symbol expressions representing DontCare
    pub dont_cares: FxHashSet<ExprRef>,

    /// FIFO source for each iterator loop in this invocation.
    pub loops: PrimaryMap<LoopId, Loop>,

    /// Initial values of persistent automaton registers.
    pub register_inits: FxHashMap<SymbolId, ExprRef>,

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
            // we can just make a fresh simplifier
            simplifier: Simplifier::new(SparseExprMap::default()),
            symbol_expr: self.symbol_expr.clone(),
            dont_cares: self.dont_cares.clone(),
            register_inits: self.register_inits.clone(),
            loops: self.loops.clone(),
            nodes: self.nodes.clone(),
            ops: self.ops.clone(),
            op_loc: self.op_loc.clone(),
        }
    }
}

impl ProtoGraph {
    pub fn new(proto_ctx: ProtocolContext) -> Self {
        let mut nodes = PrimaryMap::new();
        let entry = Node::empty();
        let entry_id: NodeId = nodes.push(entry);

        let ops = PrimaryMap::new();
        let op_loc: SecondaryMap<OpId, (usize, usize, usize)> = SecondaryMap::new();

        Self {
            proto_ctx,
            entry: entry_id,
            simplifier: Simplifier::new(SparseExprMap::default()),
            symbol_expr: FxHashMap::default(),
            dont_cares: FxHashSet::default(),
            register_inits: FxHashMap::default(),
            loops: PrimaryMap::new(),
            nodes,
            ops,
            op_loc,
        }
    }

    /// One arbitrary sample per DUT input and cycle, shared with DUT wiring.
    pub fn dont_care_input(
        &mut self,
        ctx: &mut Context,
        symbols: &SymbolTable,
        pin: SymbolId,
    ) -> ExprRef {
        let expr = ctx.bv_symbol(
            &format!("dont_care.{}", symbols[pin].name()),
            symbols[pin].tpe().bitwidth(),
        );
        self.dont_cares.insert(expr);
        expr
    }

    pub fn symbol_expr(&self, symbol_id: SymbolId) -> Option<ExprRef> {
        self.symbol_expr.get(&symbol_id).copied()
    }

    pub fn cache_symbol_expr(&mut self, symbol_id: SymbolId, expr: ExprRef) {
        self.symbol_expr.insert(symbol_id, expr);
    }

    pub fn add_register(
        &mut self,
        ctx: &mut Context,
        symbols: &mut SymbolTable,
        base: &str,
        width: u32,
    ) -> SymbolId {
        let mut suffix = 0;
        let name = loop {
            let name = if suffix == 0 {
                base.to_string()
            } else {
                format!("{base}_{suffix}")
            };
            if symbols.symbol_id_from_name_in_active_scope(&name).is_none() {
                break name;
            }
            suffix += 1;
        };
        let symbol =
            symbols.add_without_parent(name, Type::BitVec(width), SymbolKind::AutomatonState);
        let expr = ctx.bv_symbol(&symbols[symbol].full_name(symbols), width);
        self.cache_symbol_expr(symbol, expr);
        symbol
    }

    /// Visit nodes in breadth-first order from `entry`, skipping false edges
    /// Each node appears once in resulting vector, including `entry` itself
    pub fn reachable_node_ids(&self, ctx: &Context, entry: NodeId) -> Vec<NodeId> {
        let mut nodes = Vec::new();
        let mut seen = FxHashSet::from_iter([entry]);
        let mut pending = VecDeque::from([entry]);
        while let Some(node) = pending.pop_front() {
            nodes.push(node);
            for edge in &self[node].transitions {
                if edge.guard != ctx.get_false() && seen.insert(edge.target) {
                    pending.push_back(edge.target);
                }
            }
        }
        nodes
    }

    /// convenience methods for construction simplified
    /// (p AND q) or (p OR q) expressions
    pub fn and_guard(&mut self, ctx: &mut Context, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        let expr = ctx.and(lhs, rhs);
        self.simplifier.simplify(ctx, expr)
    }

    pub fn or_guard(&mut self, ctx: &mut Context, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        let expr = ctx.or(lhs, rhs);
        self.simplifier.simplify(ctx, expr)
    }

    pub fn not_guard(&mut self, ctx: &mut Context, guard: ExprRef) -> ExprRef {
        let expr = ctx.not(guard);
        self.simplifier.simplify(ctx, expr)
    }

    pub fn simplify_all_exprs(&mut self, ctx: &mut Context) {
        for (_, node) in self.nodes.iter_mut() {
            for action in &mut node.actions {
                action.guard = self.simplifier.simplify(ctx, action.guard);
            }
            for transition in &mut node.transitions {
                transition.guard = self.simplifier.simplify(ctx, transition.guard);
            }
        }

        for (_, op) in self.ops.iter_mut() {
            match op {
                Op::Assign(_, assignment) => {
                    assignment.dont_care = self.simplifier.simplify(ctx, assignment.dont_care);
                    for (guard, rhs) in &mut assignment.concretes {
                        *guard = self.simplifier.simplify(ctx, *guard);
                        *rhs = self.simplifier.simplify(ctx, *rhs);
                    }
                }
                Op::AssertEq(lhs, rhs) => {
                    *lhs = self.simplifier.simplify(ctx, *lhs);
                    *rhs = self.simplifier.simplify(ctx, *rhs);
                    debug_assert_eq!(lhs.get_type(ctx), rhs.get_type(ctx));
                }
                Op::Data { .. }
                | Op::Last { .. }
                | Op::Valid { .. }
                | Op::Fork
                | Op::InternalAssertFalse
                | Op::Done => {}
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

    /// Return this graph with a different node map and entry point.
    pub fn with_nodes(mut self, nodes: PrimaryMap<NodeId, Node>, entry: NodeId) -> Self {
        self.nodes = nodes;
        self.entry = entry;
        self
    }

    /// add a new op to the IR
    pub fn o(&mut self, op: Op) -> OpId {
        self.ops.push(op)
    }

    pub fn nodes(&self) -> impl Iterator<Item = (NodeId, &Node)> + '_ {
        self.nodes.iter()
    }

    pub fn nodes_mut(&mut self) -> impl Iterator<Item = (NodeId, &mut Node)> + '_ {
        self.nodes.iter_mut()
    }

    pub fn ops_mut(&mut self) -> impl Iterator<Item = (OpId, &mut Op)> + '_ {
        self.ops.iter_mut()
    }

    pub fn node_mut(&mut self, node_id: NodeId) -> &mut Node {
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

    /// Remove unused operations without changing node IDs or action positions.
    pub fn garbage_collect_ops(&mut self) {
        let used = self
            .nodes
            .iter()
            .flat_map(|(_, n)| n.actions.iter().map(|a| a.op))
            .collect::<FxHashSet<_>>();
        let mut mapping = FxHashMap::default();
        let mut ops = PrimaryMap::new();
        let mut locations = SecondaryMap::new();
        for (old, op) in self.ops.iter() {
            if used.contains(&old) {
                let new = ops.push(op.clone());
                mapping.insert(old, new);
                if let Some(&location) = self.op_loc.get(old) {
                    locations[new] = location;
                }
            }
        }
        for (_, node) in self.nodes.iter_mut() {
            for action in &mut node.actions {
                action.op = mapping[&action.op];
            }
        }
        self.ops = ops;
        self.op_loc = locations;
    }

    /// Rebuild the graph from the subgraph reachable from `entry`.
    /// This compacts both node IDs and op IDs.
    pub fn garbage_collect_unreachable(&mut self, ctx: &Context) -> FxHashMap<NodeId, NodeId> {
        let reachable_old_nodes = self.reachable_node_ids(ctx, self.entry);

        let mut node_map: FxHashMap<NodeId, NodeId> = FxHashMap::default();
        let mut new_nodes = PrimaryMap::new();
        for old_node_id in &reachable_old_nodes {
            let new_node_id = new_nodes.push(self.nodes[*old_node_id].clone());
            node_map.insert(*old_node_id, new_node_id);
        }

        for (_, node) in new_nodes.iter_mut() {
            node.transitions
                .retain(|transition| transition.guard != ctx.get_false());
        }

        for (_, node) in new_nodes.iter_mut() {
            for transition in &mut node.transitions {
                transition.target = node_map[&transition.target];
            }
        }
        self.entry = node_map[&self.entry];
        self.nodes = new_nodes;
        self.garbage_collect_ops();

        node_map
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
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::lowering::lower_ast_to_ir;
    use std::path::Path;
    use tempfile::NamedTempFile;

    fn parse_and_lower(source: &str) -> (Context, ProtoGraph) {
        let file = NamedTempFile::new().unwrap();
        std::fs::write(file.path(), source).unwrap();

        parse_and_lower_file(file.path(), None)
    }

    fn parse_and_lower_file(
        path: impl AsRef<Path>,
        protocol_name: Option<&str>,
    ) -> (Context, ProtoGraph) {
        let mut handler = DiagnosticHandler::default();
        let skip_static_step_fork_checks = true;
        let (mut st, modules) =
            frontend(&[&path], &mut handler, skip_static_step_fork_checks, false).unwrap();
        let module = require_single_module(modules, &[&path]).unwrap();
        let proto = match protocol_name {
            Some(protocol_name) => module
                .protos
                .into_iter()
                .find(|ast| ast.name == protocol_name)
                .unwrap(),
            None => {
                assert_eq!(module.protos.len(), 1);
                module.protos.into_iter().next().unwrap()
            }
        };
        let mut ctx = Context::default();
        let graph = lower_ast_to_ir(&mut ctx, proto, &mut st);
        (ctx, graph)
    }

    #[test]
    fn lowers_straight_line_protocol_into_distinct_ir_nodes() {
        let (ctx, ir) = parse_and_lower(
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
        assert_eq!(ir.nodes.len(), 6);
        assert_eq!(ir.ops.len(), 5);

        let entry = &ir.nodes[ir.entry];
        assert!(entry.actions.is_empty());
        assert_eq!(entry.transitions.len(), 1);
        assert_eq!(
            entry.transitions[0],
            Transition {
                guard: ctx.get_true(),
                target: NodeId(5),
                consumes_step: false,
                rotations: vec![],
            }
        );

        let init = &ir.nodes[NodeId(5)];
        assert_eq!(init.actions.len(), 1);
        assert_eq!(init.actions[0].guard, ctx.get_true());
        assert!(matches!(ir.ops[init.actions[0].op], Op::Assign(_, _)));
        assert_eq!(
            init.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(4),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let assign = &ir.nodes[NodeId(4)];
        assert_eq!(assign.actions.len(), 1);
        assert_eq!(assign.actions[0].guard, ctx.get_true());
        assert!(matches!(ir.ops[assign.actions[0].op], Op::Assign(_, _)));
        assert_eq!(
            assign.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(3),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let step = &ir.nodes[NodeId(3)];
        assert!(step.actions.is_empty());
        assert_eq!(
            step.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(2),
                consumes_step: true,
                rotations: vec![],
            }]
        );

        let assert_node = &ir.nodes[NodeId(2)];
        assert_eq!(assert_node.actions.len(), 1);
        assert_eq!(assert_node.actions[0].guard, ctx.get_true());
        assert!(matches!(
            ir.ops[assert_node.actions[0].op],
            Op::AssertEq(_, _)
        ));
        assert_eq!(
            assert_node.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(1),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 2);
        assert_eq!(exit.actions[0].guard, ctx.get_true());
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(matches!(ir.ops[exit.actions[1].op], Op::Assign(_, _)));
        assert!(exit.transitions.is_empty());
    }

    #[test]
    fn lowers_fork_into_action_and_non_step_transition() {
        let (ctx, ir) = parse_and_lower(
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

        assert_eq!(ir.nodes.len(), 4);
        assert_eq!(ir.ops.len(), 4);

        let init = &ir.nodes[NodeId(3)];
        assert_eq!(init.actions.len(), 1);
        assert!(matches!(ir.ops[init.actions[0].op], Op::Assign(_, _)));
        assert_eq!(
            init.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(2),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let fork = &ir.nodes[NodeId(2)];
        assert_eq!(fork.actions.len(), 1);
        assert!(matches!(ir.ops[fork.actions[0].op], Op::Fork));
        assert_eq!(
            fork.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(1),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 2);
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(matches!(ir.ops[exit.actions[1].op], Op::Assign(_, _)));
        assert!(exit.transitions.is_empty());
    }

    #[test]
    fn lowers_add_d1_fixture_via_parser_and_lowering() {
        let (ctx, ir) = parse_and_lower_file("../tests/adders/adder_d1/add_d1.prot", Some("add"));

        assert_eq!(ir.name, "add");
        assert_eq!(ir.args.len(), 3);
        assert_eq!(ir.nodes.len(), 11);
        assert_eq!(ir.ops.len(), 11);

        let entry = &ir.nodes[ir.entry];
        assert!(entry.actions.is_empty());
        assert_eq!(
            entry.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(10),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let init = &ir.nodes[NodeId(10)];
        assert_eq!(init.actions.len(), 2);
        assert!(matches!(ir.ops[init.actions[0].op], Op::Assign(_, _)));
        assert!(matches!(ir.ops[init.actions[1].op], Op::Assign(_, _)));
        assert_eq!(
            init.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(9),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let step = &ir.nodes[NodeId(7)];
        assert!(step.actions.is_empty());
        assert_eq!(
            step.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(6),
                consumes_step: true,
                rotations: vec![],
            }]
        );

        let fork = &ir.nodes[NodeId(3)];
        assert_eq!(fork.actions.len(), 1);
        assert!(matches!(ir.ops[fork.actions[0].op], Op::Fork));
        assert_eq!(
            fork.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(2),
                consumes_step: false,
                rotations: vec![],
            }]
        );

        let last_step = &ir.nodes[NodeId(2)];
        assert!(last_step.actions.is_empty());
        assert_eq!(
            last_step.transitions,
            vec![Transition {
                guard: ctx.get_true(),
                target: NodeId(1),
                consumes_step: true,
                rotations: vec![],
            }]
        );

        let exit = &ir.nodes[NodeId(1)];
        assert_eq!(exit.actions.len(), 3);
        assert!(matches!(ir.ops[exit.actions[0].op], Op::Done));
        assert!(matches!(ir.ops[exit.actions[1].op], Op::Assign(_, _)));
        assert!(matches!(ir.ops[exit.actions[2].op], Op::Assign(_, _)));
        assert!(exit.transitions.is_empty());
    }

    #[test]
    fn garbage_collects_unreachable_nodes_and_ops() {
        let mut pg = ProtoGraph::new(ProtocolContext::new(
            "test".into(),
            crate::frontend::symbol::ROOT_SCOPE,
        ));
        let ctx = Context::default();
        let reachable = pg.n(Node::empty());
        let unreachable = pg.n(Node::empty());

        let fork = pg.o(Op::Fork);
        let done = pg.o(Op::Done);

        let true_id = ctx.get_true();
        pg.push_action(reachable, Action::new(true_id, fork));
        pg.push_action(unreachable, Action::new(true_id, done));
        pg.push_transition(pg.entry, Transition::new(true_id, reachable, false));

        assert_eq!(pg.nodes.len(), 3);
        assert_eq!(pg.ops.len(), 2);

        pg.garbage_collect_unreachable(&ctx);

        assert_eq!(pg.nodes.len(), 2);
        assert_eq!(pg.ops.len(), 1);
        assert_eq!(pg[pg.entry].transitions.len(), 1);
    }
}
