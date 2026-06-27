// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::append_action;
use crate::ir::proto_graph::{Node as DFANode, NodeId as DFANodeId, ProtoGraph, Transition};
use cranelift_entity::EntityRef;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

/// An NFA state is a set of DFA nodes active at the same time.
type NFANode = BTreeSet<DFANodeId>;

/// Assign a dense ID to a newly discovered DFA state and queue it for processing.
fn get_or_create_state(
    set: NFANode,
    state_ids: &mut FxHashMap<NFANode, DFANodeId>,
    worklist: &mut VecDeque<NFANode>,
) -> DFANodeId {
    if let Some(id) = state_ids.get(&set) {
        return *id;
    }
    let id = DFANodeId::new(state_ids.len());
    state_ids.insert(set.clone(), id);
    worklist.push_back(set);
    id
}

/// Result of a (conservative) satisfiability check on a guard.
enum Satisfiability {
    DefinitelyUnsat,
    MaybeSat,
}

// TODO: Strengthen this with a real SAT/SMT query to prune more aggressively.
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

/// Perform subset construction
pub fn determinize(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    let mut state_ids: FxHashMap<NFANode, DFANodeId> = FxHashMap::default();
    let mut worklist: VecDeque<NFANode> = VecDeque::new();

    let start: NFANode = std::iter::once(protocol.entry).collect();
    let start_id = get_or_create_state(start, &mut state_ids, &mut worklist);

    // DFA node IDs index directly into this output vector.
    let mut new_nodes: Vec<DFANode> = Vec::new();

    // Process each reachable set of simultaneously active NFA nodes once.
    while let Some(set) = worklist.pop_front() {
        let this_id = state_ids[&set];

        // Merge actions and collect transitions from every NFA node in the set.
        let mut actions = Vec::new();
        let mut internal_assert_guard = None;
        let mut transitions = Vec::new();
        for &node_id in &set {
            for action in protocol[node_id].actions.clone() {
                append_action(
                    protocol,
                    symbols,
                    &mut actions,
                    &mut internal_assert_guard,
                    action,
                    false,
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
        let n = transitions.len();

        // Each nonzero mask selects the transitions enabled in one guard minterm.
        // TODO: Handle states with 128 or more outgoing transitions.
        assert!(n <= 128);
        for mask in 1u128..(1u128 << n) {
            let mut guard = protocol.true_id();
            let mut targets: NFANode = BTreeSet::new();
            for (i, t) in transitions.iter().enumerate() {
                let (lit, target) = (t.guard, t.target);
                let lit = if (mask >> i) & 1 == 1 {
                    targets.insert(target);
                    lit
                } else {
                    protocol.not_guard(lit)
                };
                guard = protocol.and_guard(guard, lit);
            }

            match check_sat(protocol, guard) {
                Satisfiability::DefinitelyUnsat => continue,
                Satisfiability::MaybeSat => {
                    let target_id = get_or_create_state(targets, &mut state_ids, &mut worklist);
                    new_trans.push(Transition::new(guard, target_id, true));
                }
            }
        }

        let idx = this_id.index();
        if new_nodes.len() <= idx {
            new_nodes.resize_with(idx + 1, DFANode::empty);
        }
        new_nodes[idx] = DFANode {
            actions,
            transitions: new_trans,
        };
    }

    protocol.replace_nodes(new_nodes, start_id);
}
