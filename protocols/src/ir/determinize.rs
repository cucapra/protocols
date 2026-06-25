// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

//! NFA -> DFA (subset construction) over the step-level transition graph.
//!
//! After [`crate::ir::edge_contract::contract_edges`], every transition
//! consumes a step, so a node's outgoing transitions are a nondeterministic
//! choice taken on the same cycle. This pass determinizes that choice: a DFA
//! state is a *set* of NFA nodes that are simultaneously active, its actions are
//! the union of the member nodes' actions, and its outgoing transitions are the
//! satisfiable minterms over the members' guards.
//!
//! For a node with two outgoing guards `p` and `q` this yields:
//! `p & q` -> {target_p, target_q}, `p & !q` -> {target_p}, `!p & q` ->
//! {target_q}; the `!p & !q` minterm is dead and elided. (The construction is
//! general over any number of guards, but lowering produces at most two.)
//!
//! We do not yet prune unsatisfiable minterms, nor merge conflicting actions in
//! a combined node.

use std::collections::{BTreeSet, VecDeque};

use cranelift_entity::EntityRef;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

use crate::ir::proto_graph::{Node, NodeId, ProtoGraph, Transition};

/// A DFA state: the set of NFA nodes that are active simultaneously.
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

fn not_guard(protocol: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    let negated = protocol.expr_ctx.not(guard);
    let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
    simplifier.simplify(expr_ctx, negated)
}

/// Determinize `protocol` in place via subset construction. Requires that every
/// transition consumes a step (i.e. `contract_edges` has already run).
pub fn determinize(protocol: &mut ProtoGraph) {
    let mut ids: FxHashMap<State, NodeId> = FxHashMap::default();
    let mut order: Vec<State> = Vec::new();
    let mut worklist: VecDeque<State> = VecDeque::new();

    let start: State = std::iter::once(protocol.entry).collect();
    let start_id = intern(start, &mut ids, &mut order, &mut worklist);

    // new_nodes is indexed by the (dense) DFA NodeId; we fill it as states pop.
    let mut new_nodes: Vec<Node> = Vec::new();

    while let Some(set) = worklist.pop_front() {
        let this_id = ids[&set];

        // Actions of the DFA state are the union of its members' actions; their
        // own guards already encode any internal conditionals, so we keep them
        // verbatim (no merging / dedup yet).
        let mut actions = Vec::new();
        for &node_id in &set {
            actions.extend(protocol[node_id].actions.iter().cloned());
        }

        // All outgoing transitions of all members (each consumes a step).
        let trans: Vec<Transition> = set
            .iter()
            .flat_map(|&node_id| protocol[node_id].transitions.iter().cloned())
            .collect();
        debug_assert!(
            trans.iter().all(|t| t.consumes_step),
            "determinize requires contracted (step-only) transitions"
        );

        // Enumerate the non-empty minterms over the member guards. Bit i of
        // `mask` selects guard i positively; cleared bits contribute `!guard`.
        let mut new_trans: Vec<Transition> = Vec::new();
        let n = trans.len();
        for mask in 1u32..(1u32 << n) {
            let mut guard = protocol.true_id();
            let mut targets: State = BTreeSet::new();
            for (i, t) in trans.iter().enumerate() {
                let (lit, target) = (t.guard, t.target);
                let lit = if (mask >> i) & 1 == 1 {
                    targets.insert(target);
                    lit
                } else {
                    not_guard(protocol, lit)
                };
                guard = protocol.and_guard(guard, lit);
            }
            let target_id = intern(targets, &mut ids, &mut order, &mut worklist);
            new_trans.push(Transition::new(guard, target_id, true));
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
