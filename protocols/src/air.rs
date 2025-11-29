// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Automata-based IR
//! This module contains a lower-level IR which models protocols as
//! automatas.

use crate::ir::Arg;
use patronus::expr::ExprRef;

pub struct Proto {
    name: String,
    args: Vec<Arg>,
    states: Vec<State>,
}

pub struct State {
    actions: Vec<Action>,
    edges: Vec<Edge>,
}

pub struct Edge {
    guard: ExprRef,
    is_step: bool,
}

pub struct Action {
    guard: ExprRef,
    kind: ActionKind,
}

pub enum ActionKind {
    Assign(),
    AssertEq(),
}
