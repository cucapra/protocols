use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::ReachingDefs;
use rustc_hash::{FxHashMap, FxHashSet};

pub fn propagate_assignments(
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    rd: &FxHashMap<NodeId, ReachingDefs>
) {
    let input_ports: &Vec<SymbolId> = &st
        .get_children(&pg.proto_ctx.type_param.unwrap())
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    for (id, node) in pg.nodes() {
        let assigned : Vec<SymbolId> = node.actions.iter().filter_map(|action| {
            match pg[action.op] {
                Op::Assign(sid, _) => Some(sid),
                _ => None
            }
        }).collect();

        for input in input_ports {
            if !assigned.contains(input) {
                // apply the input from the reaching definitions if only one exists

            }
        }

    }

}
