use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::edge_contract::{merge_ordered_assignment, same_assignment_target};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{
    ReachingDefs, all_ports_present, assignment_is_total, canonicalize_assignment, reachable_nodes,
};
use rustc_hash::FxHashMap;

pub fn propagate_assignments(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    rd: &FxHashMap<NodeId, ReachingDefs>,
) {
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

        let assigned: Vec<(SymbolId, usize)> = pg[id]
            .actions
            .iter()
            .enumerate()
            .filter_map(|(idx, action)| match pg[action.op] {
                Op::Assign(sid, _) => Some((sid, idx)),
                _ => None,
            })
            .collect();

        for input in &input_ports {
            let fact = node_defs
                .iter()
                .find(|(symbol_id, _)| same_assignment_target(st, **symbol_id, *input))
                .map(|(_, fact)| fact)
                .unwrap_or_else(|| panic!("missing reaching definition for {input} at {id}"));

            if let Some((assigned_symbol, action_idx)) = assigned
                .iter()
                .find(|(assigned_symbol, _)| same_assignment_target(st, *assigned_symbol, *input))
            {
                let action = pg[id].actions[*action_idx].clone();
                let Op::Assign(_, assignment) = pg[action.op].clone() else {
                    unreachable!();
                };
                let assignment_total = assignment_is_total(pg, &assignment);
                assert!(
                    !fact.conflict || assignment_total,
                    "cannot propagate assignments in {} with conflicting reaching definitions",
                    pg.proto_ctx.name
                );
                let assignment = merge_ordered_assignment(pg, fact.assignment.clone(), assignment);
                let assignment = canonicalize_assignment(pg, assignment);
                assert!(
                    assignment_is_total(pg, &assignment),
                    "cannot propagate partial assignment for {input} at {id}"
                );
                let op = pg.o(Op::Assign(*assigned_symbol, assignment));
                pg.node_mut(id).actions[*action_idx].op = op;
            } else {
                assert!(
                    !fact.conflict,
                    "cannot propagate assignments in {} with conflicting reaching definitions",
                    pg.proto_ctx.name
                );
                assert!(
                    assignment_is_total(pg, &fact.assignment),
                    "cannot propagate partial assignment for {input} at {id}"
                );
                let op = pg.o(Op::Assign(*input, fact.assignment.clone()));
                pg.push_action(id, Action::new(pg.true_id(), op));
            }
        }
    }
}
