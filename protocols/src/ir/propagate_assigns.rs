use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{AssignmentValue, ReachingDefs, all_ports_present, exists_conflicts};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn propagate_assignments(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    rd: &FxHashMap<NodeId, ReachingDefs>,
) {
    // TODO: some of the assertions in here are overkill.
    assert!(
        !exists_conflicts(rd, pg),
        "cannot propagate assignments with conflicting reaching definitions"
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

    let node_ids = pg.nodes().map(|(id, _)| id).collect::<Vec<_>>();

    for id in node_ids {
        let assigned: FxHashSet<SymbolId> = pg[id]
            .actions
            .iter()
            .filter_map(|action| match pg[action.op] {
                Op::Assign(sid, _) => Some(sid),
                _ => None,
            })
            .collect();

        for input in &input_ports {
            if assigned.contains(input) {
                continue;
            }

            // The caller should check !exists_conflicts and all_ports_present before propagation.
            let values = rd
                .get(&id)
                .and_then(|defs| defs.get(input))
                .unwrap_or_else(|| panic!("missing reaching definition for {input} at {id}"));
            assert_eq!(
                values.len(),
                1,
                "cannot propagate conflicting reaching definitions for {input} at {id}"
            );

            let def = *values.iter().next().unwrap();
            assert_eq!(
                def.guard,
                pg.true_id(),
                "cannot propagate a guarded reaching definition for {input} at {id}"
            );

            let assignment = match def.value {
                AssignmentValue::DontCare => Assignment::dont_care(pg.true_id()),
                AssignmentValue::Concrete(expr) => {
                    Assignment::concrete(pg.false_id(), pg.true_id(), expr)
                }
            };
            let op = pg.o(Op::Assign(*input, assignment));
            pg.push_action(id, Action::new(pg.true_id(), op));
        }
    }
}
