// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::SymbolTable;
use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::proto_graph::{Assignment, NodeId, ProtoGraph};
use patronus::expr::{Context, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

// Maps ports (by their `String` name`), to the existing Assignment for that port
pub type ReachingDefs = FxHashMap<String, Assignment>;

/// Nodes only store their outgoing transitions. This function precomputes and
/// returns the in-neighbors for each node.
use std::collections::VecDeque;

pub fn predecessors(pg: &ProtoGraph, start: NodeId) -> FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> {
    let mut predecessors: FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> = FxHashMap::default();
    let mut visited: FxHashSet<NodeId> = FxHashSet::default();
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

pub fn simplify_guard(ctx: &mut Context, pg: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    pg.simplifier.simplify(ctx, guard)
}

// TODO: I feel like this can be done at *merge-time* in edge-contract.rs instead
// TODO: of as a post-processing step
pub fn canonicalize_assignment(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    assignment: Assignment,
) -> Assignment {
    let dont_care = simplify_guard(ctx, pg, assignment.dont_care);
    if dont_care == ctx.get_true() {
        return Assignment {
            dont_care,
            concretes: Vec::new(),
        };
    }

    let mut prior = dont_care;
    let mut concretes: Vec<(ExprRef, ExprRef)> = Vec::new();

    for (guard, rhs) in assignment.concretes {
        let guard = simplify_guard(ctx, pg, guard);
        let not_prior = pg.not_guard(ctx, prior);
        let effective_guard = pg.and_guard(ctx, not_prior, guard);
        let effective_guard = simplify_guard(ctx, pg, effective_guard);

        match check_sat(ctx, pg, effective_guard) {
            SatResult::DefinitelyUnsat => {}
            SatResult::AlwaysSat => {
                merge_concrete_guard(ctx, pg, &mut concretes, ctx.get_true(), rhs);
                break;
            }
            SatResult::MaybeSat => {
                merge_concrete_guard(ctx, pg, &mut concretes, effective_guard, rhs);
                let next_prior = pg.or_guard(ctx, prior, effective_guard);
                prior = simplify_guard(ctx, pg, next_prior);
            }
        }

        if prior == ctx.get_true() {
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
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    concretes: &mut Vec<(ExprRef, ExprRef)>,
    guard: ExprRef,
    rhs: ExprRef,
) {
    if let Some((existing_guard, _)) = concretes
        .iter_mut()
        .find(|(_, existing_rhs)| *existing_rhs == rhs)
    {
        let merged_guard = pg.or_guard(ctx, *existing_guard, guard);
        *existing_guard = simplify_guard(ctx, pg, merged_guard);
    } else {
        concretes.push((guard, rhs));
    }
}

/// An assignment is *total* when at least one of it's guards must trigger.
/// That is, `NOT(dc_guard OR concrete_g1 OR ... OR concrete_gn)` is not satisfiable.
pub fn assignment_is_total(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    assignment: &Assignment,
) -> bool {
    let coverage = assignment
        .concretes
        .iter()
        .fold(assignment.dont_care, |coverage, (guard, _)| {
            pg.or_guard(ctx, coverage, *guard)
        });

    match check_sat(ctx, pg, coverage) {
        SatResult::AlwaysSat => true,
        SatResult::DefinitelyUnsat | SatResult::MaybeSat => false,
    }
}

/// Take `branch_guard`, i.e. a guard on an assignment and simplify it to `Some(g)`
/// under the assumption that `transition_guard` is true. If returns `None`
/// then the branch can be removed.
pub fn restrict_branch_to_edge(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    branch_guard: ExprRef,
    transition_guard: ExprRef,
) -> Option<ExprRef> {
    let overlap = pg.and_guard(ctx, branch_guard, transition_guard);
    let overlap = simplify_guard(ctx, pg, overlap);

    // are `transition_guard` and `branch_guard` mutually exclusive?
    if matches!(check_sat(ctx, pg, overlap), SatResult::DefinitelyUnsat) {
        return None;
    }

    // does `transition_guard` imply `branch_guard`?
    // t => b == NOT t OR b == NOT(t AND not B). so check t AND not B is unsat.
    let not_branch = pg.not_guard(ctx, branch_guard);
    let transition_without_branch = pg.and_guard(ctx, transition_guard, not_branch);
    if matches!(
        check_sat(ctx, pg, transition_without_branch),
        SatResult::DefinitelyUnsat
    ) {
        return Some(ctx.get_true());
    }

    // can't simplify, so we have to return the overlap
    Some(overlap)
}

pub fn format_reaching_defs(
    ctx: &Context,
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
                format_assignment(ctx, protocol, assignment),
            ));
        }
    }

    out
}

fn format_assignment(ctx: &Context, protocol: &ProtoGraph, assignment: &Assignment) -> String {
    let mut parts = Vec::new();
    if assignment.dont_care != ctx.get_false() {
        parts.push(format!(
            "X if {}",
            crate::ir::graphviz::format_expr(ctx, protocol, assignment.dont_care)
        ));
    }
    for (guard, rhs) in &assignment.concretes {
        parts.push(format!(
            "{} if {}",
            crate::ir::graphviz::format_expr(ctx, protocol, *rhs),
            crate::ir::graphviz::format_expr(ctx, protocol, *guard)
        ));
    }
    if parts.is_empty() {
        "internal_assert_false".to_string()
    } else {
        parts.join("; ")
    }
}
