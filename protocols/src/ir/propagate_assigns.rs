use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{ReachingDefs, assignment_is_total};
use cranelift_entity::EntitySet;
use rustc_hash::FxHashMap;

// BFS from the entry
pub fn reachable_node_ids(pg: &ProtoGraph, start: NodeId) -> Vec<NodeId> {
    let mut visited: EntitySet<NodeId> = EntitySet::default();
    let mut nodes = Vec::new();
    let mut q = vec![start];

    while let Some(nid) = q.pop() {
        if !visited.insert(nid) {
            continue;
        }

        nodes.push(nid);
        q.extend(
            pg[nid]
                .transitions
                .iter()
                .map(|t| t.target)
                .filter(|target| !visited.contains(*target)),
        );
    }

    nodes
}

/// check the invariant that for all nodes reachable from the entry that
/// every node has a reaching definition for every port.
fn all_ports_present(
    reaching_defs: &FxHashMap<NodeId, ReachingDefs>,
    pg: &ProtoGraph,
    st: &SymbolTable,
) -> bool {
    let input_ports: Vec<SymbolId> = st
        .get_children(&pg.proto_ctx.type_param.unwrap())
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    for nid in reachable_node_ids(pg, pg.entry) {
        let Some(rd) = reaching_defs.get(&nid) else {
            return false;
        };

        if nid == pg.entry && rd.is_empty() {
            continue;
        }

        for input in &input_ports {
            if !rd.contains_key(&st.full_name_from_symbol_id(input).to_string()) {
                return false;
            }
        }
    }

    true
}

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

    let node_ids = reachable_node_ids(pg, pg.entry);

    for id in node_ids {
        let Some(node_defs) = rd.get(&id) else {
            continue;
        };
        if id == pg.entry && node_defs.is_empty() {
            continue;
        }

        let actions = pg[id]
            .actions
            .iter()
            .filter(|&action| !matches!(pg[action.op], Op::Assign(_, _)))
            .cloned()
            .collect();

        pg.node_mut(id).actions = actions;

        for input in &input_ports {
            let assignment = node_defs
                .get(&st.full_name_from_symbol_id(input))
                .unwrap_or_else(|| panic!("missing reaching definition for {input} at {id}"));
            assert!(
                assignment_is_total(pg, assignment),
                "cannot propagate partial assignment for {input} at {id}"
            );

            let op = pg.o(Op::Assign(*input, assignment.clone()));
            pg.push_action(id, Action::new(pg.true_id(), op));
        }
    }
}
