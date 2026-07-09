use std::borrow::Cow;
use baa::WidthInt;
use itertools::Itertools;
use patronus::expr::{ExprRef, Type};
use patronus::system::{TransitionSystem, State};
use rustc_hash::FxHashMap;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::ProtoGraph;
use crate::PortId;

struct NodeTransition {
    pub guard: ExprRef,
    pub src: ExprRef,
    pub dst: ExprRef,
}

pub fn into_transition_system(
    mut pg: ProtoGraph,
    mut ts: TransitionSystem,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    st: &SymbolTable,
) -> (patronus::expr::Context, TransitionSystem) {
    let mut ctx = std::mem::take(&mut pg.expr_ctx);

    let node_count = pg.nodes().try_len().unwrap() as u64;
    let width = u64::from(u64::BITS - node_count.leading_zeros());

    let s = ctx.string(Cow::from("node"));
    let node_sym = ctx.symbol(s, Type::BV(width as WidthInt));

    // the initial node state is the entry
    let entry_id = ctx.bit_vec_val(
        pg.entry.as_u32(),
        width
    );

    let mut transitions: Vec<NodeTransition> = vec![];
    // create the transition function - only use the reachable nodes for efficiency
    let mut q = vec![pg.entry];
    while let Some(id) = q.pop() {
        let src = ctx.bit_vec_val(id.as_u32(), width);
        for (guard, dst_node) in pg[id].transitions.iter().map(|t| (t.guard, t.target)) {
            let dst = ctx.bit_vec_val(dst_node.as_u32(), width);

            let t = NodeTransition { guard, src , dst};
            transitions.push(t);
        }
    }

    // add the "node" state and the transition function for it
    let node_state = State {
        symbol: node_sym,
        init: Some(entry_id),
        next: None,
    };

    ts.add_state(&ctx, node_state);
    (ctx, ts)
}
