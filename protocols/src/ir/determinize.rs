// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::append_action;
use crate::ir::proto_graph::{Node as NFANode, NodeId, ProtoGraph, Transition};
use cranelift_entity::PrimaryMap;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

/// A DFA Node is a set of NFA nodes active at the same time.
type DFANode = BTreeSet<NodeId>;

fn get_or_create_state(
    dfa_node: DFANode,
    subset_nodes: &mut FxHashMap<DFANode, NodeId>,
    worklist: &mut VecDeque<DFANode>,
    new_nodes: &mut PrimaryMap<NodeId, NFANode>,
) -> NodeId {
    // if we've already seen this combination of NFA states, return the existing node
    if let Some(id) = subset_nodes.get(&dfa_node) {
        return *id;
    }

    // otherwise allocate a new DFA node
    let id = new_nodes.push(NFANode::empty());
    subset_nodes.insert(dfa_node.clone(), id);
    worklist.push_back(dfa_node);
    id
}

/// Result of a (conservative) satisfiability check on a guard.
pub enum SatResult {
    DefinitelyUnsat,
    MaybeSat,
    DefinitelySat,
}

// TODO: Strengthen this with a real SAT/SMT query to prune more aggressively.
pub fn check_sat(protocol: &mut ProtoGraph, guard: ExprRef) -> SatResult {
    let simplified = {
        let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
        simplifier.simplify(expr_ctx, guard)
    };

    if simplified == protocol.false_id() {
        SatResult::DefinitelyUnsat
    } else if simplified == protocol.true_id() {
        SatResult::DefinitelySat
    } else {
        SatResult::MaybeSat
    }
}

/// Perform subset construction.
pub fn determinized(protocol: ProtoGraph, symbols: &SymbolTable) -> ProtoGraph {
    let mut protocol = protocol.clone();
    let start: DFANode = BTreeSet::from([protocol.entry]);
    let mut state_ids: FxHashMap<DFANode, NodeId> = FxHashMap::default();
    let mut worklist: VecDeque<DFANode> = VecDeque::new();
    let mut new_nodes: PrimaryMap<NodeId, NFANode> = PrimaryMap::new();
    let start_id = get_or_create_state(start, &mut state_ids, &mut worklist, &mut new_nodes);

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
                    &mut protocol,
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
            let mut targets: DFANode = BTreeSet::new();
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

            let guard = match check_sat(&mut protocol, guard) {
                SatResult::DefinitelyUnsat => continue,
                SatResult::DefinitelySat => protocol.true_id(),
                SatResult::MaybeSat => guard,
            };

            {
                let target_id =
                    get_or_create_state(targets, &mut state_ids, &mut worklist, &mut new_nodes);
                new_trans.push(Transition::new(guard, target_id, true));
            }
        }

        new_nodes[this_id] = NFANode {
            actions,
            transitions: new_trans,
        };
    }

    // TODO: this function requires cloning twice. the benefit is that we don't add a weird
    // method to ProtoGraph that swaps a set of nodes (seems very contrived)? Ask Kevin what the
    // best idiom for this is.
    let mut protocol = protocol.with_nodes(new_nodes, start_id);
    protocol.simplify_all_exprs();
    protocol
}
