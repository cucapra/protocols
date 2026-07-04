// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph};
use itertools::Itertools;
use patronus::expr::ExprRef;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignmentValue {
    DontCare,
    Concrete(ExprRef),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentDef {
    pub guard: ExprRef,
    pub value: AssignmentValue,
}

pub type ReachingDefs = FxHashMap<SymbolId, FxHashSet<AssignmentDef>>;

/// Nodes only store their outgoing transitions. This function precomputes and returns
/// the in-neighbors for each node that is reachable from the entry.
pub(crate) fn reachable_nodes(pg: &ProtoGraph) -> FxHashSet<NodeId> {
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

fn predecessors(
    pg: &ProtoGraph,
    reachable: &FxHashSet<NodeId>,
) -> FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> {
    let mut predecessors: FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> = FxHashMap::default();

    for n in reachable {
        for t in pg[n].clone().transitions {
            if reachable.contains(&t.target) {
                predecessors.entry(t.target).or_default().push((*n, t.guard));
            }
        }
    }

    predecessors
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

    // by default, the entry node begins with
    let mut in_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();
    in_defs.insert(
        pg.entry,
        input_ports
            .iter()
            .map(|sym_id| {
                (
                    *sym_id,
                    FxHashSet::from_iter([AssignmentDef {
                        guard: pg.true_id(),
                        value: AssignmentValue::DontCare,
                    }]),
                )
            })
            .collect(),
    );

    let mut out_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();

    let mut worklist: Vec<NodeId> = reachable.iter().copied().collect();

    while let Some(id) = worklist.pop() {
        // run the merge function with its predecessors to get in_defs[n]
        // merge function is just the union
        let mut merged = ReachingDefs::default();
        for (pred_id, transition_guard) in preds.get(&id).into_iter().flatten() {
            if let Some(pred_defs) = out_defs.get(pred_id) {
                for (symbol_id, values) in pred_defs {
                    for def in values {
                        let and_guard = pg.and_guard(def.guard, *transition_guard);
                        let guard = match check_sat(pg, and_guard) {
                            SatResult::DefinitelyUnsat => continue,
                            SatResult::DefinitelySat => pg.true_id(),
                            SatResult::MaybeSat => {
                                let not_def_guard = pg.not_guard(def.guard);
                                let transition_without_def =
                                    pg.and_guard(*transition_guard, not_def_guard);
                                match check_sat(pg, transition_without_def) {
                                    SatResult::DefinitelyUnsat => pg.true_id(),
                                    SatResult::DefinitelySat | SatResult::MaybeSat => def.guard,
                                }
                            }
                        };
                        merged.entry(*symbol_id).or_default().insert(AssignmentDef {
                            guard,
                            value: def.value,
                        });
                    }
                }
            }
        }
        // in defs for the entry is predefined
        if id != pg.entry {
            in_defs.insert(id, merged);
        }

        // run the transfer function on it to get out_defs[n]
        // TODO: I wonder if this is more confusing than just having a regular loop
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
            let old_defs = out.remove(&symbol_id).unwrap_or_default();
            let mut new_defs = FxHashSet::default();
            let mut coverage = assignment.dont_care;

            match check_sat(pg, assignment.dont_care) {
                SatResult::DefinitelySat => {
                    out.insert(
                        symbol_id,
                        FxHashSet::from_iter([AssignmentDef {
                            guard: pg.true_id(),
                            value: AssignmentValue::DontCare,
                        }]),
                    );
                    continue;
                }
                SatResult::MaybeSat => {
                    new_defs.insert(AssignmentDef {
                        guard: assignment.dont_care,
                        value: AssignmentValue::DontCare,
                    });
                }
                SatResult::DefinitelyUnsat => (),
            }

            let mut prior = assignment.dont_care;
            for (guard, val) in assignment.concretes {
                let effective_guard = {
                    let not_prior = pg.not_guard(prior);
                    pg.and_guard(not_prior, guard)
                };

                match check_sat(pg, effective_guard) {
                    SatResult::DefinitelySat => {
                        new_defs = FxHashSet::from_iter([AssignmentDef {
                            guard: pg.true_id(),
                            value: AssignmentValue::Concrete(val),
                        }]);
                        coverage = pg.true_id();
                        break;
                    }
                    SatResult::MaybeSat => {
                        new_defs.insert(AssignmentDef {
                            guard: effective_guard,
                            value: AssignmentValue::Concrete(val),
                        });
                    }
                    SatResult::DefinitelyUnsat => (),
                }

                prior = pg.or_guard(prior, guard);
                coverage = pg.or_guard(coverage, guard);
            }

            let not_covered = pg.not_guard(coverage);
            for old_def in old_defs {
                let fallback_guard = pg.and_guard(old_def.guard, not_covered);
                let fallback_guard = match check_sat(pg, fallback_guard) {
                    SatResult::DefinitelyUnsat => continue,
                    SatResult::DefinitelySat => pg.true_id(),
                    SatResult::MaybeSat => fallback_guard,
                };
                new_defs.insert(AssignmentDef {
                    guard: fallback_guard,
                    value: old_def.value,
                });
            }

            out.insert(symbol_id, new_defs);
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

    in_defs
}

/// Returns `true` if any port at any node has more than one reaching assignment,
/// or if the unique reaching assignment is not unconditional.
pub fn exists_conflicts(reaching_defs: &FxHashMap<NodeId, ReachingDefs>, pg: &ProtoGraph) -> bool {
    for rd in reaching_defs.values() {
        for set in rd.values() {
            if set.len() > 1 {
                return true;
            }
            if let Some(def) = set.iter().next() {
                if def.guard != pg.true_id() {
                    return true;
                }
            }
        }
    }

    false
}

pub fn all_ports_present(
    reaching_defs: &FxHashMap<NodeId, ReachingDefs>,
    pg: &ProtoGraph,
    st: &SymbolTable,
) -> bool {
    // TODO: maybe make this a helper in pg context or something
    let input_ports: &Vec<SymbolId> = &st
        .get_children(&pg.proto_ctx.type_param.unwrap())
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    let reachable = reachable_nodes(pg);

    // all reachable nodes have all ports present
    for rd in reaching_defs.values() {
        for input in input_ports {
            if !rd.contains_key(&input) {
                return false;
            }
        }
    }

    // all reachable nodes present
    for id in reachable {
        if !reaching_defs.contains_key(&id) {
            return false;
        }
    }

    true
}

pub fn format_reaching_defs(
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
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
        symbol_defs.sort_by_key(|(symbol_id, _)| symbols.full_name_from_symbol_id(symbol_id));

        for (symbol_id, values) in symbol_defs {
            let mut values = values
                .iter()
                .map(|def| format_assignment_def(protocol, *def))
                .collect::<Vec<_>>();
            values.sort();
            out.push_str(&format!(
                "  {}: {}\n",
                symbols.full_name_from_symbol_id(symbol_id),
                values.join(", ")
            ));
        }
    }

    out
}

fn format_assignment_def(protocol: &ProtoGraph, def: AssignmentDef) -> String {
    let value = match def.value {
        AssignmentValue::DontCare => "X".to_string(),
        AssignmentValue::Concrete(expr) => crate::ir::graphviz::format_expr(protocol, expr),
    };

    if def.guard == protocol.true_id() {
        value
    } else {
        format!("{value} if {}", crate::ir::graphviz::format_expr(protocol, def.guard))
    }
}
