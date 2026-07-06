use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::edge_contract::same_assignment_target;
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{
    ReachingDefs, all_ports_present, assignment_is_total, reachable_nodes,
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

        retain_non_input_assignments(pg, st, id, &input_ports);

        for input in &input_ports {
            let fact = lookup_fact(node_defs, st, *input)
                .unwrap_or_else(|| panic!("missing reaching definition for {input} at {id}"));
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

fn lookup_fact<'a>(
    defs: &'a ReachingDefs,
    st: &SymbolTable,
    input: SymbolId,
) -> Option<&'a crate::ir::reaching_defs::ReachingFact> {
    defs.iter()
        .find(|(symbol_id, _)| same_assignment_target(st, **symbol_id, input))
        .map(|(_, fact)| fact)
}

fn retain_non_input_assignments(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    id: NodeId,
    input_ports: &[SymbolId],
) {
    let actions = pg[id]
        .actions
        .iter()
        .cloned()
        .filter(|action| match pg[action.op] {
            Op::Assign(symbol_id, _) => !input_ports
                .iter()
                .any(|input| same_assignment_target(st, symbol_id, *input)),
            _ => true,
        })
        .collect();

    pg.node_mut(id).actions = actions;
}
