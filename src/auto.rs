// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use crate::ir::{SymbolTable, Transaction};
use cranelift_entity::{entity_impl, PrimaryMap};
use patronus::expr::{Context, ExprRef};

struct Automaton {
    name: String,
    /// states
    states: PrimaryMap<StateId, State>,
    /// starting state
    start: StateId,
    /// input variables
    inputs: Vec<ExprRef>,
    /// output variables
    outputs: Vec<ExprRef>,
}

impl Automaton {
    fn new(ctx: &Context, name: impl ToString) -> Self {
        let mut states = PrimaryMap::new();
        let start = states.push(State::new(ctx, "start"));
        Self {
            name: name.to_string(),
            states,
            start,
            inputs: vec![],
            outputs: vec![],
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StateId(u32);
entity_impl!(StateId, "state");

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct State {
    name: String,
    /// transitions from this state
    trans: Vec<Tran>,
    /// constraints on the dut io
    constraints: Vec<ExprRef>,
    /// first time mapping of outputs / inputs
    mappings: Vec<ExprRef>,
    /// condition under which this is the end state
    done: ExprRef,
}

impl State {
    fn new(ctx: &Context, name: impl ToString) -> Self {
        Self {
            name: name.to_string(),
            trans: Vec::default(),
            constraints: Vec::default(),
            mappings: Vec::default(),
            done: ctx.tru(),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Tran {
    to: StateId,
    cond: ExprRef,
    steps: u16,
}

fn convert(symbols: &SymbolTable, tran: &Transaction) -> Automaton {
    let mut ctx = Context::default();
    let mut a = Automaton::new(&ctx, &tran.name);

    a
}

/// convert an automaton into a dot file to use with graphviz
fn to_dot(a: &Automaton) {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::tests::build_add_transaction;

    #[test]
    fn test_convert_calyx_go_done() {
        let (_, symbols, add) = build_add_transaction();
        let a = convert(&symbols, &add);
    }
}
