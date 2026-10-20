// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::ProtocolContext;
use crate::frontend::symbol::SymbolId;
use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use patronus::expr::{
    Context, ExprRef, Simplifier, SparseExprMap, TypeCheck, simple_transform_expr
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
pub enum LoopSource {
    Sequence(SymbolId),
    /// A scalar argument or literal; its value is the number of dummy entries.
    Repeat(ExprRef),
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
// A node is a (logically) unordered set of actions and transitions
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
    /// Head signals for one loop. They all describe the same item; reading a
    /// signal does not itself advance the sequence. There is no FIFO operand.
    Data {
        loop_id: LoopId,
        result: ExprRef,
    },
    Last {
        loop_id: LoopId,
        result: ExprRef,
    },
    Valid {
        loop_id: LoopId,
        result: ExprRef,
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
            Self::Data { loop_id, result } => Self::Data {
                loop_id: *loop_id,
                result: remap_expr(ctx, *result, substitutions),
            },
            Self::Last { loop_id, result } => Self::Last {
                loop_id: *loop_id,
                result: remap_expr(ctx, *result, substitutions),
            },
            Self::Valid { loop_id, result } => Self::Valid {
                loop_id: *loop_id,
                result: remap_expr(ctx, *result, substitutions),
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

    pub loops: PrimaryMap<LoopId, LoopSource>,
    /// Next-value assignment target -> initial value of its physical register.
    /// Generated state is separate from sticky DUT input assignments.
    pub register_inits: FxHashMap<SymbolId, ExprRef>,
    /// Next-value assignment target -> current register value expression.
    /// The current value is a state input; the assigned next value is a wire.
    /// These are distinct logical signals connected to one physical register.
    pub register_inputs: FxHashMap<SymbolId, ExprRef>,

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
            loops: self.loops.clone(),
            register_inits: self.register_inits.clone(),
            register_inputs: self.register_inputs.clone(),
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
            loops: PrimaryMap::new(),
            register_inits: FxHashMap::default(),
            register_inputs: FxHashMap::default(),
            nodes,
            ops,
            op_loc,
        }
    }

    pub fn symbol_expr(&self, symbol_id: SymbolId) -> Option<ExprRef> {
        self.symbol_expr.get(&symbol_id).copied()
    }

    pub fn cache_symbol_expr(&mut self, symbol_id: SymbolId, expr: ExprRef) {
        self.symbol_expr.insert(symbol_id, expr);
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
                Op::Data { .. } | Op::Last { .. } | Op::Valid { .. } => {}
                Op::Fork | Op::InternalAssertFalse | Op::Done => {}
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

    /// Rebuild the graph from the subgraph reachable from `entry`.
    /// This compacts both node IDs and op IDs.
    pub fn garbage_collect_unreachable(&mut self, ctx: &Context) -> FxHashMap<NodeId, NodeId> {
        let mut reachable_old_nodes = Vec::new();
        let mut seen = FxHashSet::default();
        let mut q = VecDeque::from([self.entry]);

        while let Some(node_id) = q.pop_front() {
            if !seen.insert(node_id) {
                continue;
            }
            reachable_old_nodes.push(node_id);
            for transition in &self.nodes[node_id].transitions {
                if transition.guard != ctx.get_false() {
                    q.push_back(transition.target);
                }
            }
        }

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

        let mut reachable_old_ops = Vec::new();
        let mut seen_ops = FxHashSet::default();
        for (_, node) in new_nodes.iter() {
            for action in &node.actions {
                if seen_ops.insert(action.op) {
                    reachable_old_ops.push(action.op);
                }
            }
        }

        let mut op_map: FxHashMap<OpId, OpId> = FxHashMap::default();
        let mut new_ops = PrimaryMap::new();
        let mut new_op_loc = SecondaryMap::new();
        for old_op_id in reachable_old_ops {
            let new_op_id = new_ops.push(self.ops[old_op_id].clone());
            op_map.insert(old_op_id, new_op_id);
            if let Some(loc) = self.op_loc.get(old_op_id).copied() {
                new_op_loc[new_op_id] = loc;
            }
        }

        for (_, node) in new_nodes.iter_mut() {
            for action in &mut node.actions {
                action.op = op_map[&action.op];
            }
            for transition in &mut node.transitions {
                transition.target = node_map[&transition.target];
            }
        }

        self.entry = node_map[&self.entry];
        self.nodes = new_nodes;
        self.ops = new_ops;
        self.op_loc = new_op_loc;

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
