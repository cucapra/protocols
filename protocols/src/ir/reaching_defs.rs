// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::edge_contract::{merge_ordered_assignment, merge_unordered_assignment};
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use itertools::Itertools;
use patronus::expr::ExprRef;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, PartialEq, Eq)]
pub struct ReachingFact {
    pub assignment: Assignment,
    pub conflict: bool,
}

pub type ReachingDefs = FxHashMap<String, ReachingFact>;

// TODO: let's write a pruner before running the analysis?
pub fn reachable_nodes(pg: &ProtoGraph) -> FxHashSet<NodeId> {
    let mut reachable = FxHashSet::default();
    let mut q = vec![pg.entry];

    while let Some(n) = q.pop() {
        if !reachable.insert(n) {
            continue;
        }

        for t in pg[n].clone().transitions {
            q.push(t.target);
        }
    }

    reachable
}

/// Nodes only store their outgoing transitions. This function precomputes and returns
/// the in-neighbors for each node that is reachable from the entry.
fn predecessors(
    pg: &ProtoGraph,
    reachable: &FxHashSet<NodeId>,
) -> FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> {
    let mut predecessors: FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> = FxHashMap::default();

    for n in reachable {
        for t in pg[n].clone().transitions {
            if reachable.contains(&t.target) {
                predecessors
                    .entry(t.target)
                    .or_default()
                    .push((*n, t.guard));
            }
        }
    }

    predecessors
}

fn simplify_guard(pg: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    let (expr_ctx, simplifier) = (&mut pg.expr_ctx, &mut pg.simplifier);
    simplifier.simplify(expr_ctx, guard)
}

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
            SatResult::DefinitelySat => {
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

fn assignment_coverage(pg: &mut ProtoGraph, assignment: &Assignment) -> ExprRef {
    let coverage = assignment
        .concretes
        .iter()
        .fold(assignment.dont_care, |coverage, (guard, _)| {
            pg.or_guard(coverage, *guard)
        });
    simplify_guard(pg, coverage)
}

pub fn assignment_is_total(pg: &mut ProtoGraph, assignment: &Assignment) -> bool {
    let coverage = assignment_coverage(pg, assignment);
    match check_sat(pg, coverage) {
        SatResult::DefinitelySat => true,
        SatResult::DefinitelyUnsat | SatResult::MaybeSat => false,
    }
}

fn restrict_branch_to_edge(
    pg: &mut ProtoGraph,
    branch_guard: ExprRef,
    transition_guard: ExprRef,
) -> Option<ExprRef> {
    let overlap = pg.and_guard(branch_guard, transition_guard);
    let overlap = simplify_guard(pg, overlap);
    match check_sat(pg, overlap) {
        SatResult::DefinitelyUnsat => return None,
        SatResult::DefinitelySat | SatResult::MaybeSat => {}
    }

    let not_branch = pg.not_guard(branch_guard);
    let transition_without_branch = pg.and_guard(transition_guard, not_branch);
    match check_sat(pg, transition_without_branch) {
        SatResult::DefinitelyUnsat => Some(pg.true_id()),
        SatResult::DefinitelySat | SatResult::MaybeSat => Some(overlap),
    }
}

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

fn merge_fact(pg: &mut ProtoGraph, existing: ReachingFact, new: ReachingFact) -> ReachingFact {
    let mut internal_assert_guard = None;
    let assignment = merge_unordered_assignment(
        pg,
        &mut internal_assert_guard,
        existing.assignment,
        new.assignment,
    );
    let has_conflict = internal_assert_guard
        .map(|guard| !matches!(check_sat(pg, guard), SatResult::DefinitelyUnsat))
        .unwrap_or(false);

    ReachingFact {
        assignment: canonicalize_assignment(pg, assignment),
        conflict: existing.conflict || new.conflict || has_conflict,
    }
}

fn transfer_fact(
    pg: &mut ProtoGraph,
    existing: ReachingFact,
    assignment: Assignment,
) -> ReachingFact {
    let assignment_is_total = assignment_is_total(pg, &assignment);
    let assignment = merge_ordered_assignment(pg, existing.assignment, assignment);
    ReachingFact {
        assignment: canonicalize_assignment(pg, assignment),
        conflict: existing.conflict && !assignment_is_total,
    }
}

pub fn reaching_definitions(
    // it's a bit of a shame that we have to pass a mutable graph for an analysis, but the
    // sat checker mutates expressions by simplifying them
    pg: &mut ProtoGraph,
    st: &SymbolTable,
) -> FxHashMap<NodeId, ReachingDefs> {
    let reachable = reachable_nodes(pg);
    let preds = predecessors(pg, &reachable);

    let dut = pg.type_param.expect("protocol has no DUT");
    let input_ports: Vec<SymbolId> = st
        .get_children(&dut)
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    let mut in_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();
    in_defs.insert(
        pg.entry,
        input_ports
            .iter()
            .map(|sym_id| {
                (
                    st.full_name_from_symbol_id(sym_id).to_string(),
                    ReachingFact {
                        assignment: Assignment::dont_care(pg.true_id()),
                        conflict: false,
                    },
                )
            })
            .collect(),
    );

    let mut out_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();
    let mut worklist: Vec<NodeId> = reachable.iter().copied().collect();

    while let Some(id) = worklist.pop() {
        let mut merged = ReachingDefs::default();
        for (pred_id, transition_guard) in preds.get(&id).into_iter().flatten() {
            if let Some(pred_defs) = out_defs.get(pred_id) {
                for (symbol_name, fact) in pred_defs {
                    let assignment =
                        restrict_assignment_to_edge(pg, fact.assignment.clone(), *transition_guard);

                    // don't insert a ReachingFact for a fully empty assignment
                    if assignment.dont_care == pg.false_id() && assignment.concretes.is_empty() {
                        continue;
                    }

                    let edge_fact = ReachingFact {
                        assignment,
                        conflict: fact.conflict,
                    };

                    merged
                        .entry(symbol_name.clone())
                        .and_modify(|existing| {
                            *existing = merge_fact(pg, existing.clone(), edge_fact.clone());
                        })
                        .or_insert(edge_fact);
                }
            }
        }

        if id != pg.entry {
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
            let existing = out.remove(&key).unwrap_or_else(|| ReachingFact {
                assignment: Assignment {
                    dont_care: pg.false_id(),
                    concretes: Vec::new(),
                },
                conflict: false,
            });
            out.insert(key, transfer_fact(pg, existing, assignment));
        }

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

        for (symbol_name, fact) in symbol_defs {
            let conflict = if fact.conflict { " conflict" } else { "" };
            out.push_str(&format!(
                "  {}: {}{}\n",
                symbol_name,
                format_assignment(protocol, &fact.assignment),
                conflict
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
