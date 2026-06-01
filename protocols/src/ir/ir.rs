// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl};
use crate::frontend::serialize::{build_statements, serialize_expr};
use crate::frontend::symbol::{Arg, SymbolId, SymbolTable, Type};
use crate::frontend::ast::*;

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
pub struct Action(ExprId, OpId);

#[derive(Debug, Clone, PartialEq, Eq)]
/// A Transition is a guard, a target node, and flag if this transition consumes step
pub struct Transition(ExprId, NodeId, bool);

#[derive(Debug, Clone, PartialEq, Eq)]
// A node is a (logically) unorded set of actions and transitions
pub struct Node(Vec<Action>, Vec<Transition>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Assign(SymbolId, ExprId),
    AssertEq(ExprId, ExprId), 
    Fork,
    Done
}

#[derive(Debug, Clone, PartialEq, Eq)]
// TODO: A lot of this is metadata shared between the AST and IR.
// I wonder if it is worth factoring out a metadata between the AST and IR.
pub struct Protocol {
    /// The name of the `Protocol`
    pub name: String,

    /// List of `Arg`s to the `Protocol`
    pub args: Vec<Arg>,

    /// The entrypoint of the `Protocol`
    pub entry: NodeId,

    /// Optional type parameter (identified by its `SymbolId`)
    pub type_param: Option<SymbolId>,

    /// Whether the protocol has been marked as `idle` with `#[idle]`
    pub is_idle: bool,

    /// Maps `ExprId`s to their corresponding `Expr`s
    exprs: PrimaryMap<ExprId, Expr>,

    /// The distinguished `ExprId` corresponding to `DontCare`
    dont_care_id: ExprId,

    /// Maps `NodeId`s to their corresponding `Node`s
    nodes: PrimaryMap<NodeId, Node>,

    /// Maps `OpId`s to their corresponding `Op`s
    ops: PrimaryMap<OpId, Op>,

    /// Debug Info
    expr_loc: SecondaryMap<ExprId, (usize, usize, usize)>,
    op_loc: SecondaryMap<StmtId, Option<(usize, usize, usize)>>,
}