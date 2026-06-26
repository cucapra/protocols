// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use std::collections::{BTreeSet, VecDeque};

use cranelift_entity::EntityRef;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::append_action_with_unordered_assignment_merge;
use crate::ir::proto_graph::{Action, Node, NodeId, Op, ProtoGraph, Transition};

/// A DFA state: set of nodes from the NFA
type State = BTreeSet<NodeId>;

/// Intern a DFA state, assigning it a fresh (dense, allocation-order) `NodeId`
/// and queueing it for processing the first time it is seen.
fn intern(
    set: State,
    ids: &mut FxHashMap<State, NodeId>,
    order: &mut Vec<State>,
    worklist: &mut VecDeque<State>,
) -> NodeId {
    if let Some(id) = ids.get(&set) {
        return *id;
    }
    let id = NodeId::new(order.len());
    ids.insert(set.clone(), id);
    order.push(set.clone());
    worklist.push_back(set);
    id
}

// TODO: move into ProtoGraph?
fn not_guard(protocol: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    let negated = protocol.expr_ctx.not(guard);
    let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
    simplifier.simplify(expr_ctx, negated)
}

/// Result of a (conservative) satisfiability check on a guard.
enum Satisfiability {
    DefinitelyUnsat,
    MaybeSat,
}

// TODO: consider strengthen this (e.g. a real SAT/SMT query) to prune more aggressively.
fn check_sat(protocol: &mut ProtoGraph, guard: ExprRef) -> Satisfiability {
    let simplified = {
        let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
        simplifier.simplify(expr_ctx, guard)
    };
    if simplified == protocol.false_id() {
        Satisfiability::DefinitelyUnsat
    } else {
        Satisfiability::MaybeSat
    }
}

fn has_done_action(protocol: &ProtoGraph, actions: &[Action]) -> bool {
    actions
        .iter()
        .any(|action| matches!(protocol[action.op], Op::Done))
}

/// Determinize `protocol` in place via subset construction. Requires that every
/// transition consumes a step (i.e. `contract_edges` has already run).
pub fn determinize(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    let mut ids: FxHashMap<State, NodeId> = FxHashMap::default();
    let mut order: Vec<State> = Vec::new();
    let mut worklist: VecDeque<State> = VecDeque::new();

    let start: State = std::iter::once(protocol.entry).collect();
    let start_id = intern(start, &mut ids, &mut order, &mut worklist);

    // new_nodes is indexed by the DFA NodeId; we fill it as states pop.
    let mut new_nodes: Vec<Node> = Vec::new();

    while let Some(set) = worklist.pop_front() {
        let this_id = ids[&set];
        // println!("worklist length: {}", worklist.len());
        // Take the union of transitions
        // Take the union of actions, except assignments are merged.
        let mut actions = Vec::new();
        let mut internal_assert_guard = None;
        let mut transitions = Vec::new();
        for &node_id in &set {
            for action in protocol[node_id].actions.clone() {
                append_action_with_unordered_assignment_merge(
                    protocol,
                    symbols,
                    &mut actions,
                    &mut internal_assert_guard,
                    action,
                );
            }
            transitions.extend(protocol[node_id].transitions.iter().cloned());
        }
        if let Some(internal_assert_guard) = internal_assert_guard {
            let internal_assert_op = protocol.o(crate::ir::proto_graph::Op::InternalAssertFalse);
            actions.push(crate::ir::proto_graph::Action::new(
                internal_assert_guard,
                internal_assert_op,
            ));
        }

        let mut new_trans: Vec<Transition> = Vec::new();

        if !has_done_action(protocol, &actions) {
            // Enumerate the non-empty minterms over the member guards.
            let n = transitions.len();

            // mask gives us every permutation of 0s and 1s for `n` outgoing transitions
            // 0 means NOT(transition), 1 means transition
            for mask in 1u32..(1u32 << n) {
                let mut guard = protocol.true_id();
                let mut targets: State = BTreeSet::new();
                for (i, t) in transitions.iter().enumerate() {
                    let (lit, target) = (t.guard, t.target);
                    let lit = if (mask >> i) & 1 == 1 {
                        targets.insert(target);
                        lit
                    } else {
                        not_guard(protocol, lit)
                    };
                    guard = protocol.and_guard(guard, lit);
                }

                match check_sat(protocol, guard) {
                    Satisfiability::DefinitelyUnsat => continue,
                    Satisfiability::MaybeSat => {
                        let target_id = intern(targets, &mut ids, &mut order, &mut worklist);
                        new_trans.push(Transition::new(guard, target_id, true));
                    }
                }
            }
        }

        let idx = this_id.index();
        if new_nodes.len() <= idx {
            new_nodes.resize_with(idx + 1, Node::empty);
        }
        new_nodes[idx] = Node {
            actions,
            transitions: new_trans,
        };
    }

    protocol.replace_nodes(new_nodes, start_id);
}
