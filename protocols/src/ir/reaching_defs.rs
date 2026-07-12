// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::SymbolTable;
use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::edge_contract::{merge_ordered_assignment, merge_unordered_assignment};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use itertools::Itertools;
use patronus::expr::ExprRef;
use rustc_hash::{FxHashMap, FxHashSet};

// Maps ports (by their `String` name`), to the existing Assignment for that port
pub type ReachingDefs = FxHashMap<String, Assignment>;

/// Nodes only store their outgoing transitions. This function precomputes and
/// returns the in-neighbors for each node.
use std::collections::{HashSet, VecDeque};

pub fn predecessors(pg: &ProtoGraph, start: NodeId) -> FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> {
    let mut predecessors: FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> = FxHashMap::default();
    let mut visited: HashSet<NodeId> = HashSet::default();
    let mut queue: VecDeque<NodeId> = VecDeque::new();

    // Start BFS from the given node
    queue.push_back(start);
    visited.insert(start);

    while let Some(current_node) = queue.pop_front() {
        // For each transition from current node
        for t in pg[current_node].clone().transitions {
            let target = t.target;

            // Add predecessor relationship
            predecessors
                .entry(target)
                .or_default()
                .push((current_node, t.guard));

            // If we haven't visited this node yet, add it to queue
            if !visited.contains(&target) {
                visited.insert(target);
                queue.push_back(target);
            }
        }
    }

    predecessors
}

pub fn simplify_guard(pg: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    let (expr_ctx, simplifier) = (&mut pg.expr_ctx, &mut pg.simplifier);
    simplifier.simplify(expr_ctx, guard)
}

// TODO: I feel like this can be done at *merge-time* in edge-contract.rs instead
// TODO: of as a post-processing step
pub fn canonicalize_assignment(pg: &mut ProtoGraph, assignment: Assignment) -> Assignment {
    let dont_care = simplify_guard(pg, assignment.dont_care);
    if dont_care == pg.true_id() {
        return Assignment {
            dont_care,
            concretes: Vec::new(),
        };
    }

    let mut prior = dont_care;
    let mut concretes: Vec<(ExprRef, ExprRef)> = Vec::new();

    for (guard, rhs) in assignment.concretes {
        let guard = simplify_guard(pg, guard);
        let not_prior = pg.not_guard(prior);
        let effective_guard = pg.and_guard(not_prior, guard);
        let effective_guard = simplify_guard(pg, effective_guard);

        match check_sat(pg, effective_guard) {
            SatResult::DefinitelyUnsat => {}
            SatResult::AlwaysSat => {
                merge_concrete_guard(pg, &mut concretes, pg.true_id(), rhs);
                break;
            }
            SatResult::MaybeSat => {
                merge_concrete_guard(pg, &mut concretes, effective_guard, rhs);
                let next_prior = pg.or_guard(prior, effective_guard);
                prior = simplify_guard(pg, next_prior);
            }
        }

        if prior == pg.true_id() {
            break;
        }
    }

    Assignment {
        dont_care,
        concretes,
    }
}

/// if the `rhs` already exists in `concretes` with guard `old_guard`
/// `guard` should be an *effective* guard, so that performing
/// `old_guard || guard` does not violate merge semantics
fn merge_concrete_guard(
    pg: &mut ProtoGraph,
    concretes: &mut Vec<(ExprRef, ExprRef)>,
    guard: ExprRef,
    rhs: ExprRef,
) {
    if let Some((existing_guard, _)) = concretes
        .iter_mut()
        .find(|(_, existing_rhs)| *existing_rhs == rhs)
    {
        let merged_guard = pg.or_guard(*existing_guard, guard);
        *existing_guard = simplify_guard(pg, merged_guard);
    } else {
        concretes.push((guard, rhs));
    }
}

/// An assignment is *total* when at least one of it's guards must trigger.
/// That is, `NOT(dc_guard OR concrete_g1 OR ... OR concrete_gn)` is not satisfiable.
pub fn assignment_is_total(pg: &mut ProtoGraph, assignment: &Assignment) -> bool {
    let coverage = assignment
        .concretes
        .iter()
        .fold(assignment.dont_care, |coverage, (guard, _)| {
            pg.or_guard(coverage, *guard)
        });

    match check_sat(pg, coverage) {
        SatResult::AlwaysSat => true,
        SatResult::DefinitelyUnsat | SatResult::MaybeSat => false,
    }
}

/// Take `branch_guard`, i.e. a guard on an assignment and simplify it to `Some(g)`
/// under the assumption that `transition_guard` is true. If returns `None`
/// then the branch can be removed.
pub fn restrict_branch_to_edge(
    pg: &mut ProtoGraph,
    branch_guard: ExprRef,
    transition_guard: ExprRef,
) -> Option<ExprRef> {
    let overlap = pg.and_guard(branch_guard, transition_guard);
    let overlap = simplify_guard(pg, overlap);

    // are `transition_guard` and `branch_guard` mutually exclusive?
    if matches!(check_sat(pg, overlap), SatResult::DefinitelyUnsat) {
        return None;
    }

    // does `transition_guard` imply `branch_guard`?
    // t => b == NOT t OR b == NOT(t AND not B). so check t AND not B is unsat.
    let not_branch = pg.not_guard(branch_guard);
    let transition_without_branch = pg.and_guard(transition_guard, not_branch);
    if matches!(
        check_sat(pg, transition_without_branch),
        SatResult::DefinitelyUnsat
    ) {
        return Some(pg.true_id());
    }

    // can't simplify, so we have to return the overlap
    Some(overlap)
}

/// For each branch of `assignment`, rewrite it under the assumption that
/// `transition_guard` is true.
fn restrict_assignment_to_edge(
    pg: &mut ProtoGraph,
    assignment: Assignment,
    transition_guard: ExprRef,
) -> Assignment {
    let assignment = canonicalize_assignment(pg, assignment);
    let dont_care = restrict_branch_to_edge(pg, assignment.dont_care, transition_guard)
        .unwrap_or(pg.false_id());
    let concretes = assignment
        .concretes
        .into_iter()
        .filter_map(|(guard, rhs)| {
            restrict_branch_to_edge(pg, guard, transition_guard).map(|guard| (guard, rhs))
        })
        .collect();

    canonicalize_assignment(
        pg,
        Assignment {
            dont_care,
            concretes,
        },
    )
}

/// Returns `true` if this assignment might produce multiple different values
fn has_multiple_outcomes(pg: &mut ProtoGraph, assignment: &Assignment) -> bool {
    let canonicalized = canonicalize_assignment(pg, assignment.clone());
    canonicalized.concretes.len() + usize::from(canonicalized.dont_care != pg.false_id()) > 1
}

// the binary merge function for reaching definitions analysis is just `merge_unordered_assignment`
fn merge_assignment(pg: &mut ProtoGraph, existing: Assignment, new: Assignment) -> Assignment {
    let assignment = merge_unordered_assignment(pg, &mut None, existing, new);
    canonicalize_assignment(pg, assignment)
}

// the binary transfer function for reaching definitions analysis is just `merge_ordered_assignment`
fn transfer_assignment(
    pg: &mut ProtoGraph,
    existing: Assignment,
    assignment: Assignment,
) -> Assignment {
    let assignment = merge_ordered_assignment(pg, existing, assignment);
    canonicalize_assignment(pg, assignment)
}

pub fn reaching_definitions(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
) -> FxHashMap<NodeId, ReachingDefs> {
    reaching_definitions_from(pg, st, pg.entry)
}

pub fn reaching_definitions_from(
    // TODO: it's a bit of a shame that we have to pass a mutable graph for an analysis,
    // but the SAT checker mutates expressions by simplifying them
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    start: NodeId,
) -> FxHashMap<NodeId, ReachingDefs> {
    let preds = predecessors(pg, start);
    let mut in_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();
    let mut out_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();

    // worklist by default is all reachable nodes.
    // let mut worklist: Vec<NodeId> = reachable.iter().copied().collect();
    let mut worklist: Vec<NodeId> = reachable_node_ids(pg, start);

    while let Some(id) = worklist.pop() {
        let mut merged = ReachingDefs::default();
        let mut incoming_conflicts = FxHashSet::default();
        for (pred_id, transition_guard) in preds.get(&id).into_iter().flatten() {
            if let Some(pred_defs) = out_defs.get(pred_id) {
                for (symbol_name, pred_assignment) in pred_defs {
                    let assignment =
                        restrict_assignment_to_edge(pg, pred_assignment.clone(), *transition_guard);

                    // don't insert a reaching definition for a fully empty assignment
                    if assignment.dont_care == pg.false_id() && assignment.concretes.is_empty() {
                        continue;
                    }

                    merged
                        .entry(symbol_name.clone())
                        .and_modify(|existing| {
                            *existing = merge_assignment(pg, existing.clone(), assignment.clone());
                            if has_multiple_outcomes(pg, existing) {
                                incoming_conflicts.insert(symbol_name.clone());
                            }
                        })
                        .or_insert(assignment);
                }
            }
        }

        if id != start {
            in_defs.insert(id, merged);
        }

        let assignments = pg[id]
            .actions
            .iter()
            .filter_map(|a| match pg[a.op].clone() {
                Op::Assign(symbol_id, assignment) => Some((symbol_id, assignment)),
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut out = in_defs.get(&id).cloned().unwrap_or_default();

        for (symbol_id, assignment) in assignments {
            let key = st.full_name_from_symbol_id(&symbol_id).to_string();
            let existing = out.remove(&key).unwrap_or_else(|| Assignment {
                dont_care: pg.false_id(),
                concretes: Vec::new(),
            });
            incoming_conflicts.remove(&key);
            out.insert(key, transfer_assignment(pg, existing, assignment));
        }

        assert!(
            incoming_conflicts.is_empty(),
            "reaching definition conflict remains after transfer at {id}"
        );

        if out_defs.get(&id) != Some(&out) {
            out_defs.insert(id, out);

            worklist.extend(
                pg[id]
                    .clone()
                    .transitions
                    .into_iter()
                    .map(|t| t.target)
                    .unique(),
            );
        }
    }

    out_defs
}

pub fn format_reaching_defs(
    protocol: &ProtoGraph,
    _symbols: &SymbolTable,
    reaching_defs: &FxHashMap<NodeId, ReachingDefs>,
) -> String {
    let mut out = String::new();
    let mut node_ids = reaching_defs.keys().copied().collect::<Vec<_>>();
    node_ids.sort();

    for node_id in node_ids {
        out.push_str(&format!("{node_id}:\n"));
        let Some(defs) = reaching_defs.get(&node_id) else {
            continue;
        };

        let mut symbol_defs = defs.iter().collect::<Vec<_>>();
        symbol_defs.sort_by_key(|(symbol_name, _)| *symbol_name);

        for (symbol_name, assignment) in symbol_defs {
            out.push_str(&format!(
                "  {}: {}\n",
                symbol_name,
                format_assignment(protocol, assignment),
            ));
        }
    }

    out
}

fn format_assignment(protocol: &ProtoGraph, assignment: &Assignment) -> String {
    let mut parts = Vec::new();
    if assignment.dont_care != protocol.false_id() {
        parts.push(format!(
            "X if {}",
            crate::ir::graphviz::format_expr(protocol, assignment.dont_care)
        ));
    }
    for (guard, rhs) in &assignment.concretes {
        parts.push(format!(
            "{} if {}",
            crate::ir::graphviz::format_expr(protocol, *rhs),
            crate::ir::graphviz::format_expr(protocol, *guard)
        ));
    }
    if parts.is_empty() {
        "internal_assert_false".to_string()
    } else {
        parts.join("; ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::ROOT_SCOPE;

    fn test_graph() -> ProtoGraph {
        ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE))
    }

    fn concrete_assignment(pg: &ProtoGraph, guard: ExprRef, rhs: ExprRef) -> Assignment {
        Assignment::concrete(pg.false_id(), guard, rhs)
    }

    #[test]
    fn merge_flags_multiple_reaching_concretes_even_when_guards_are_exclusive() {
        let mut pg = test_graph();
        let p = pg.expr_ctx.bv_symbol("p", 1);
        let not_p = pg.not_guard(p);
        let one = pg.expr_ctx.bv_symbol("one", 1);
        let zero = pg.expr_ctx.bv_symbol("zero", 1);

        let from_a = concrete_assignment(&pg, p, one);
        let from_b = concrete_assignment(&pg, not_p, zero);

        let merged = merge_assignment(&mut pg, from_a, from_b);

        assert!(has_multiple_outcomes(&mut pg, &merged));
        assert_eq!(merged.dont_care, pg.false_id());
        assert_eq!(merged.concretes.len(), 2);
    }

    #[test]
    fn merge_flags_maybe_overlapping_reaching_definitions() {
        let mut pg = test_graph();
        let p = pg.expr_ctx.bv_symbol("p", 1);
        let q = pg.expr_ctx.bv_symbol("q", 1);
        let one = pg.expr_ctx.bv_symbol("one", 1);
        let zero = pg.expr_ctx.bv_symbol("zero", 1);

        let from_a = concrete_assignment(&pg, p, one);
        let from_b = concrete_assignment(&pg, q, zero);

        let merged = merge_assignment(&mut pg, from_a, from_b);

        assert!(has_multiple_outcomes(&mut pg, &merged));
        assert_eq!(merged.dont_care, pg.false_id());
        assert_eq!(merged.concretes.len(), 2);
    }

    #[test]
    fn total_assignment_kills_incoming_reaching_definition_conflict() {
        let mut pg = test_graph();
        let p = pg.expr_ctx.bv_symbol("p", 1);
        let q = pg.expr_ctx.bv_symbol("q", 1);
        let one = pg.expr_ctx.bv_symbol("one", 1);
        let zero = pg.expr_ctx.bv_symbol("zero", 1);
        let two = pg.expr_ctx.bv_symbol("two", 1);

        let from_a = concrete_assignment(&pg, p, one);
        let from_b = concrete_assignment(&pg, q, zero);
        let conflicted = merge_assignment(&mut pg, from_a, from_b);
        assert!(has_multiple_outcomes(&mut pg, &conflicted));

        let reassignment = concrete_assignment(&pg, pg.true_id(), two);
        let transferred = transfer_assignment(&mut pg, conflicted, reassignment);

        assert!(assignment_is_total(&mut pg, &transferred));
    }
}
