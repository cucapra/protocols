// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::append_action;
use crate::ir::proto_graph::{Node as NFANode, NodeId, ProtoGraph, Transition};
use cranelift_entity::PrimaryMap;
use patronus::expr::{Expr, ExprRef, TypeCheck, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};

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
    AlwaysSat,
}

fn collect_boolean_atoms(protocol: &ProtoGraph, expr: ExprRef, atoms: &mut FxHashSet<ExprRef>) {
    if expr == protocol.true_id() || expr == protocol.false_id() {
        return;
    }
    match protocol.expr_ctx[expr] {
        Expr::BVAnd(lhs, rhs, 1) | Expr::BVOr(lhs, rhs, 1) => {
            collect_boolean_atoms(protocol, lhs, atoms);
            collect_boolean_atoms(protocol, rhs, atoms);
        }
        Expr::BVNot(inner, 1) => collect_boolean_atoms(protocol, inner, atoms),
        _ => {
            atoms.insert(expr);
        }
    }
}

fn eval_boolean_skeleton(
    protocol: &ProtoGraph,
    expr: ExprRef,
    values: &FxHashMap<ExprRef, bool>,
) -> bool {
    if expr == protocol.true_id() {
        return true;
    }
    if expr == protocol.false_id() {
        return false;
    }
    match protocol.expr_ctx[expr] {
        Expr::BVAnd(lhs, rhs, 1) => {
            eval_boolean_skeleton(protocol, lhs, values)
                && eval_boolean_skeleton(protocol, rhs, values)
        }
        Expr::BVOr(lhs, rhs, 1) => {
            eval_boolean_skeleton(protocol, lhs, values)
                || eval_boolean_skeleton(protocol, rhs, values)
        }
        Expr::BVNot(inner, 1) => !eval_boolean_skeleton(protocol, inner, values),
        _ => values[&expr],
    }
}

fn propositionally_unsat(protocol: &ProtoGraph, expr: ExprRef) -> bool {
    let mut atoms = FxHashSet::default();
    collect_boolean_atoms(protocol, expr, &mut atoms);
    // Keep this lightweight. Falling back to MaybeSat is always sound.
    if atoms.len() > 16 {
        return false;
    }
    let atoms: Vec<_> = atoms.into_iter().collect();
    for mask in 0usize..(1usize << atoms.len()) {
        let values = atoms
            .iter()
            .enumerate()
            .map(|(index, atom)| (*atom, (mask >> index) & 1 == 1))
            .collect();
        if eval_boolean_skeleton(protocol, expr, &values) {
            return false;
        }
    }
    true
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
        SatResult::AlwaysSat
    } else if propositionally_unsat(protocol, simplified) {
        SatResult::DefinitelyUnsat
    } else {
        let negated = protocol.not_guard(simplified);
        if propositionally_unsat(protocol, negated) {
            SatResult::AlwaysSat
        } else {
            SatResult::MaybeSat
        }
    }
}

fn transition_guards_after_node_updates(
    protocol: &mut ProtoGraph,
    actions: &[crate::ir::proto_graph::Action],
    transitions: &[Transition],
) -> Vec<ExprRef> {
    let mut substitutions = FxHashMap::default();

    for action in actions {
        let crate::ir::proto_graph::Op::Assign(symbol, assignment) = protocol[action.op].clone()
        else {
            continue;
        };
        if !protocol.state_init.contains_key(&symbol) || assignment.dont_care != protocol.false_id()
        {
            continue;
        }
        let Some(lhs) = protocol.symbol_expr(symbol) else {
            continue;
        };
        let prior = substitutions.get(&lhs).copied().unwrap_or(lhs);
        let action_guard = simple_transform_expr(
            &mut protocol.expr_ctx,
            action.guard,
            |_ctx, candidate, _children| substitutions.get(&candidate).copied(),
        );
        let branches: Vec<_> = assignment
            .concretes
            .iter()
            .map(|(guard, rhs)| {
                (
                    simple_transform_expr(
                        &mut protocol.expr_ctx,
                        *guard,
                        |_ctx, candidate, _children| substitutions.get(&candidate).copied(),
                    ),
                    simple_transform_expr(
                        &mut protocol.expr_ctx,
                        *rhs,
                        |_ctx, candidate, _children| substitutions.get(&candidate).copied(),
                    ),
                )
            })
            .collect();

        // Assignment branches use first-match priority. If no branch fires,
        // monitor state holds its old value.
        let mut next = prior;
        for (branch_guard, rhs) in branches.into_iter().rev() {
            let guard = protocol.and_guard(action_guard, branch_guard);
            next = if lhs.is_bool(&protocol.expr_ctx) {
                let when_set = protocol.and_guard(guard, rhs);
                let not_guard = protocol.not_guard(guard);
                let when_held = protocol.and_guard(not_guard, next);
                protocol.or_guard(when_set, when_held)
            } else {
                protocol.expr_ctx.ite(guard, rhs, next)
            };
        }
        substitutions.insert(lhs, next);
    }

    transitions
        .iter()
        .map(|transition| {
            let guard = simple_transform_expr(
                &mut protocol.expr_ctx,
                transition.guard,
                |_ctx, candidate, _children| substitutions.get(&candidate).copied(),
            );
            protocol.simplifier.simplify(&mut protocol.expr_ctx, guard)
        })
        .collect()
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

        // The DFA successor only records which NFA target nodes are active,
        // not which of several parallel edges activated each target. Collapse
        // those parallel edges before enumerating subsets. Otherwise every
        // equivalent edge selection becomes a separate minterm which is later
        // ORed back together into a very large expression.
        let mut grouped: Vec<Transition> = Vec::new();
        for transition in transitions {
            if let Some(existing) = grouped
                .iter_mut()
                .find(|existing| existing.target == transition.target)
            {
                existing.guard = protocol.or_guard(existing.guard, transition.guard);
            } else {
                grouped.push(transition);
            }
        }
        let transitions = grouped;

        if let Some(first) = transitions.first()
            && transitions
                .iter()
                .all(|transition| transition.target == first.target)
        {
            let guard = transitions
                .iter()
                .fold(protocol.false_id(), |guard, transition| {
                    protocol.or_guard(guard, transition.guard)
                });
            let target = BTreeSet::from([first.target]);
            let target_id =
                get_or_create_state(target, &mut state_ids, &mut worklist, &mut new_nodes);
            new_nodes[this_id] = NFANode {
                actions,
                transitions: vec![Transition::new(guard, target_id, true)],
            };
            continue;
        }

        let mut new_trans: Vec<Transition> = Vec::new();
        let n = transitions.len();
        let analysis_guards =
            transition_guards_after_node_updates(&mut protocol, &actions, &transitions);
        let mut mutually_exclusive = vec![vec![false; n]; n];
        for i in 0..n {
            for j in (i + 1)..n {
                let overlap = protocol.and_guard(analysis_guards[i], analysis_guards[j]);
                let disjoint = matches!(
                    check_sat(&mut protocol, overlap),
                    SatResult::DefinitelyUnsat
                );
                mutually_exclusive[i][j] = disjoint;
                mutually_exclusive[j][i] = disjoint;
            }
        }

        // Each nonzero mask selects the transitions enabled in one guard minterm.
        // TODO: Handle states with 128 or more outgoing transitions.
        assert!(n <= 128);
        for mask in 1u128..(1u128 << n) {
            let mut guard = protocol.true_id();
            let mut analysis_guard = protocol.true_id();
            let mut targets: DFANode = BTreeSet::new();
            for (i, t) in transitions.iter().enumerate() {
                let selected = (mask >> i) & 1 == 1;
                let (lit, analysis_lit) = if selected {
                    targets.insert(t.target);
                    (t.guard, analysis_guards[i])
                } else if (0..n).any(|j| (mask >> j) & 1 == 1 && mutually_exclusive[i][j]) {
                    // A selected transition already implies that this guard is
                    // false, so its negation would only add expression noise.
                    continue;
                } else {
                    (
                        protocol.not_guard(t.guard),
                        protocol.not_guard(analysis_guards[i]),
                    )
                };
                guard = protocol.and_guard(guard, lit);
                analysis_guard = protocol.and_guard(analysis_guard, analysis_lit);
            }

            match check_sat(&mut protocol, analysis_guard) {
                SatResult::DefinitelyUnsat => continue,
                SatResult::AlwaysSat | SatResult::MaybeSat => {}
            }

            let target_id =
                get_or_create_state(targets, &mut state_ids, &mut worklist, &mut new_nodes);
            if let Some(existing) = new_trans
                .iter_mut()
                .find(|transition| transition.target == target_id && transition.consumes_step)
            {
                existing.guard = protocol.or_guard(existing.guard, guard);
            } else {
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
