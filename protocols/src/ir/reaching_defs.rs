// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::interpreter::Value as WaveValue;
use crate::ir::proto_graph::{Node, NodeId, ProtoGraph};
use rustc_hash::FxHashMap;

/// Nodes only store their outgoing transitions. This function precomputes and returns
/// the in-neighbors for each node that is reachable from the entry.
fn predecessors(pg : &ProtoGraph) -> FxHashMap<NodeId, Vec<NodeId>> {
    let mut predecessors : FxHashMap<NodeId, Vec<NodeId>> = FxHashMap::default();
    let mut q = vec![pg.entry];

    while let Some(n) = q.pop() {
        // n is a predecessor of t
        for t in pg[n].clone().transitions {
            predecessors.entry(n).and_modify(|v| v.push(t.target));
            q.push(t.target);
        }
    }

    predecessors
}

pub fn reaching_definitions(
    pg: &ProtoGraph,
    st: &SymbolTable,
) -> FxHashMap<NodeId, Vec<(SymbolId, WaveValue)>> {
    let preds = predecessors(pg);

    let dut = pg.type_param.expect("protocol has no DUT");
    let input_ports: Vec<SymbolId> = st
        .get_children(&dut)
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    // by default, the entry node begins with
    let mut in_defs: FxHashMap<NodeId, Vec<(SymbolId, WaveValue)>> = FxHashMap::default();
    in_defs.insert(
        pg.entry,
        input_ports
            .iter()
            .map(|sym_id| (*sym_id, WaveValue::DontCare))
            .collect(),
    );

    let out_defs : FxHashMap<NodeId, Vec<(SymbolId, WaveValue)>> = FxHashMap::default();

    let mut worklist: Vec<(NodeId, &Node)> = pg.nodes().collect::<Vec<(NodeId, &Node)>>();

    while let Some((id, _)) = worklist.pop() {
        // run the merge function with its predecessors to get in_defs[n]
        // merge function is just the union
        let merged : Vec<(SymbolId, WaveValue)> = preds[&id].iter().map(|nid| out_defs[nid].clone()).flatten().collect();
        in_defs.insert(id, merged);

        // run  the transfer function on it to get out_defs[n]
        // if an assignment is definitely satisfiable, then remove all the other assignments

        // if out b changed, add the successors to the worklist
    }


    FxHashMap::default()
}
