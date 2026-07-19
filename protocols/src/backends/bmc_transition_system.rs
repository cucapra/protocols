use crate::PortId;
use crate::backends::transition_system::{
    IfThenExpr, if_thens_to_ite, lower_proto_graph_to_transition_system,
};
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::proto_graph::{Op, ProtoGraph};
use baa::WidthInt;
use patronus::expr::{Context, ExprRef};
use patronus::system::{Output, TransitionSystem};
use rustc_hash::{FxHashMap, FxHashSet};
use std::borrow::Cow;

fn symbol_bitvec_expr(
    ctx: &mut Context,
    st: &SymbolTable,
    symbol_id: SymbolId,
    instance: usize,
) -> ExprRef {
    let full_name = st.full_name_from_symbol_id(&symbol_id);
    let expr_name = if matches!(st[symbol_id].kind(), SymbolKind::Arg(_)) {
        format!("{full_name}#{instance}")
    } else {
        full_name.clone()
    };
    match st[symbol_id].tpe() {
        crate::frontend::symbol::Type::BitVec(width) => {
            ctx.bv_symbol(&expr_name, width as WidthInt)
        }
        _ => panic!("unsupported input type for {}", full_name),
    }
}

pub struct LoweredSystemResult {
    pub ctx: Context,
    pub ts: TransitionSystem,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub protocol_inputs: FxHashMap<(usize, SymbolId), ExprRef>,
    pub protocol_choices: Vec<ExprRef>,
    pub node_symbol: ExprRef,
    pub done_state: Option<ExprRef>,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
    pub fork_ready: ExprRef,
}

pub fn into_bmc_transition_system(
    mut pg: ProtoGraph,
    mut ts: TransitionSystem,
    proto_choices: Vec<ExprRef>,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    st: &SymbolTable,
) -> LoweredSystemResult {
    let mut ctx = std::mem::take(&mut pg.expr_ctx);

    let mut protocol_inputs = FxHashMap::default();
    let mut added_protocol_inputs = FxHashSet::default();
    for (instance, proto_choice) in proto_choices.iter().enumerate() {
        ts.add_input(&ctx, *proto_choice);
        for symbol_id in st.get_args() {
            if !matches!(st[symbol_id].kind(), SymbolKind::Arg(_)) {
                continue;
            }
            let expr = symbol_bitvec_expr(&mut ctx, st, symbol_id, instance);
            if added_protocol_inputs.insert(expr) {
                ts.add_input(&ctx, expr);
            }
            protocol_inputs.insert((instance, symbol_id), expr);
        }
    }

    // add an output for if we're ready to fork
    let fork_ready_str = ctx.string(Cow::from("fork_ready"));
    let mut fork_ready_ite = ctx.bit_vec_val(0, 1);

    let core =
        lower_proto_graph_to_transition_system(pg, ctx, ts, symbol_to_port, port_to_expr, st);
    let mut ctx = core.ctx;
    let mut ts = core.ts;

    // fork output logic
    let mut forks = Vec::new();

    for id in &core.reachable_nodes {
        let node_id_expr = ctx.bit_vec_val(id.as_u32(), core.node_id_width);
        let node_equals = ctx.equal(core.node_symbol, node_id_expr);

        for action in &core.pg[*id].actions {
            if matches!(core.pg[action.op], Op::Fork) {
                let guard = ctx.and(node_equals, action.guard);
                forks.push(IfThenExpr {
                    if_cond: guard,
                    then: ctx.bit_vec_val(1, 1),
                });
            }
        }
    }

    fork_ready_ite = if_thens_to_ite(forks, &mut ctx, fork_ready_ite);

    // make the output for fork_ready
    let fork_choice_output = Output {
        name: fork_ready_str,
        expr: fork_ready_ite,
    };
    ts.outputs.push(fork_choice_output);

    LoweredSystemResult {
        ctx,
        ts,
        port_to_expr: core.port_to_expr,
        protocol_inputs,
        protocol_choices: proto_choices,
        node_symbol: core.node_symbol,
        done_state: Some(core.done_state),
        external_assert_state: core.external_assert_state,
        internal_assert_state: core.internal_assert_state,
        is_dont_care: core.is_dont_care,
        fork_ready: fork_ready_ite,
    }
}
