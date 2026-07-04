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
fn predecessors(pg: &ProtoGraph) -> FxHashMap<NodeId, Vec<NodeId>> {
    let mut predecessors: FxHashMap<NodeId, Vec<NodeId>> = FxHashMap::default();
    let mut q = vec![pg.entry];

    let mut visited: FxHashSet<NodeId> = FxHashSet::default();
    while let Some(n) = q.pop() {
        visited.insert(n);

        // n is a predecessor of t
        for t in pg[n].clone().transitions {
            predecessors.entry(t.target).or_default().push(n);

            if !visited.contains(&t.target) {
                q.push(t.target);
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
    let preds = predecessors(pg);

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

    let mut worklist: Vec<NodeId> = pg.nodes().map(|(id, _)| id).collect();

    while let Some(id) = worklist.pop() {
        // run the merge function with its predecessors to get in_defs[n]
        // merge function is just the union
        let mut merged = ReachingDefs::default();
        for pred_id in preds.get(&id).into_iter().flatten() {
            if let Some(pred_defs) = out_defs.get(pred_id) {
                for (symbol_id, values) in pred_defs {
                    merged
                        .entry(*symbol_id)
                        .or_default()
                        .extend(values.iter().copied());
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
            // if an assignment is definitely satisfiable, then remove all the other assignments
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
                    out.entry(symbol_id).or_default().insert(AssignmentDef {
                        guard: assignment.dont_care,
                        value: AssignmentValue::DontCare,
                    });
                }
                SatResult::DefinitelyUnsat => (),
            }

            for (guard, val) in assignment.concretes {
                match check_sat(pg, guard) {
                    SatResult::DefinitelySat => {
                        out.insert(
                            symbol_id,
                            FxHashSet::from_iter([AssignmentDef {
                                guard: pg.true_id(),
                                value: AssignmentValue::Concrete(val),
                            }]),
                        );
                        break;
                    }
                    SatResult::MaybeSat => {
                        out.entry(symbol_id).or_default().insert(AssignmentDef {
                            guard,
                            value: AssignmentValue::Concrete(val),
                        });
                    }
                    SatResult::DefinitelyUnsat => (),
                }
            }
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

    // all ports present
    for rd in reaching_defs.values() {
        for input in input_ports {
            if !rd.contains_key(&input) {
                return false;
            }
        }
    }

    // all nodes present
    for (id, _) in pg.nodes() {
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
