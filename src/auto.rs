// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use cranelift_entity::{entity_impl, PrimaryMap};
use patronus::expr::ExprRef;

struct Automaton {
    /// states
    states: PrimaryMap<StateId, State>,
    /// starting state
    start: StateId,
    /// input variables
    inputs: Vec<ExprRef>,
    /// output variables
    outputs: Vec<ExprRef>,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StateId(u32);
entity_impl!(StateId, "state");

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct State {
    /// transitions from this state
    trans: Vec<Tran>,
    /// constraints on the dut io
    constraints: Vec<ExprRef>,
    /// first time mapping of outputs / inputs
    mappings: Vec<ExprRef>,
    /// condition under which this is the end state
    done: ExprRef,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Tran {
    to: StateId,
    cond: ExprRef,
    steps: u16,
}
