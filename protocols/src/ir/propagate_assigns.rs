use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{
    AssignmentDef, AssignmentValue, ReachingDefs, all_ports_present, exists_conflicts,
    reachable_nodes,
};
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

fn raw_coverage(pg: &mut ProtoGraph, assignment: &Assignment) -> ExprRef {
    assignment
        .concretes
        .iter()
        .fold(assignment.dont_care, |coverage, (guard, _)| {
            pg.or_guard(coverage, *guard)
        })
}

fn assignment_from_reaching_def(pg: &ProtoGraph, def: AssignmentDef) -> Assignment {
    assert_eq!(
        def.guard,
        pg.true_id(),
        "cannot propagate a guarded reaching definition"
    );

    match def.value {
        AssignmentValue::DontCare => Assignment::dont_care(pg.true_id()),
        AssignmentValue::Concrete(expr) => Assignment::concrete(pg.false_id(), pg.true_id(), expr),
    }
}

fn add_fallback(pg: &mut ProtoGraph, mut assignment: Assignment, def: AssignmentDef) -> Assignment {
    assert_eq!(
        def.guard,
        pg.true_id(),
        "cannot propagate a guarded reaching definition"
    );

    match def.value {
        AssignmentValue::DontCare => {
            let coverage = raw_coverage(pg, &assignment);
            let fallback_guard = pg.not_guard(coverage);
            assignment.dont_care = pg.or_guard(assignment.dont_care, fallback_guard);
        }
        AssignmentValue::Concrete(expr) => {
            assignment.concretes.push((pg.true_id(), expr));
        }
    }

    assignment
}

pub fn propagate_assignments(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    rd: &FxHashMap<NodeId, ReachingDefs>,
) {
    // TODO: some of the assertions in here are overkill.
    assert!(
        !exists_conflicts(rd, pg),
        "{}", format!("cannot propagate assignments in {} with conflicting reaching definitions", pg.proto_ctx.name), 
    );
    assert!(
        all_ports_present(rd, pg, st),
        "cannot propagate assignments unless all ports are present at all nodes"
    );

    let input_ports: Vec<SymbolId> = st
        .get_children(&pg.proto_ctx.type_param.unwrap())
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    let node_ids = reachable_nodes(pg).into_iter().collect::<Vec<_>>();

    for id in node_ids {
        let Some(node_defs) = rd.get(&id) else {
            continue;
        };

        let assigned: FxHashMap<SymbolId, usize> = pg[id]
            .actions
            .iter()
            .enumerate()
            .filter_map(|(idx, action)| match pg[action.op] {
                Op::Assign(sid, _) => Some((sid, idx)),
                _ => None,
            })
            .collect();

        for input in &input_ports {
            let values = node_defs
                .get(input)
                .unwrap_or_else(|| panic!("missing reaching definition for {input} at {id}"));
            assert_eq!(
                values.len(),
                1,
                "cannot propagate conflicting reaching definitions for {input} at {id}"
            );

            let def = *values.iter().next().unwrap();

            if let Some(action_idx) = assigned.get(input) {
                let action = pg[id].actions[*action_idx].clone();
                let Op::Assign(_, assignment) = pg[action.op].clone() else {
                    unreachable!();
                };
                let assignment = add_fallback(pg, assignment, def);
                let op = pg.o(Op::Assign(*input, assignment));
                pg.node_mut(id).actions[*action_idx].op = op;
            } else {
                let assignment = assignment_from_reaching_def(pg, def);
                let op = pg.o(Op::Assign(*input, assignment));
                pg.push_action(id, Action::new(pg.true_id(), op));
            }
        }
    }
}
