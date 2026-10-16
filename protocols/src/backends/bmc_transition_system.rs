use crate::PortId;
use crate::backends::transition_system::lower_proto_graph_to_transition_system;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::proto_graph::ProtoGraph;
use baa::WidthInt;
use patronus::expr::{Context, ExprRef};
use patronus::system::TransitionSystem;
use rustc_hash::{FxHashMap, FxHashSet};

fn symbol_bitvec_expr(
    ctx: &mut Context,
    symbols: &SymbolTable,
    symbol: SymbolId,
    instance: usize,
) -> ExprRef {
    let full_name = symbols.full_name_from_symbol_id(&symbol);
    let name = if matches!(symbols[symbol].kind(), SymbolKind::Arg(_)) {
        format!("{full_name}#{instance}")
    } else {
        full_name.clone()
    };
    match symbols[symbol].tpe() {
        crate::frontend::symbol::Type::BitVec(width) => ctx.bv_symbol(&name, width as WidthInt),
        other => panic!("unsupported bounded-driver input type {other:?} for {full_name}"),
    }
}

pub struct LoweredSystemResult {
    pub ts: TransitionSystem,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub protocol_inputs: FxHashMap<(usize, SymbolId), ExprRef>,
    pub protocol_choices: Vec<ExprRef>,
    pub node_symbol: ExprRef,
    pub done_state: Option<ExprRef>,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
}

#[allow(clippy::too_many_arguments)]
pub fn into_bmc_transition_system(
    expr_ctx: &mut Context,
    graph: ProtoGraph,
    mut system: TransitionSystem,
    protocol_choices: Vec<ExprRef>,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    protocol_arg_symbols: &[SymbolId],
    symbols: &SymbolTable,
) -> LoweredSystemResult {
    let mut protocol_inputs = FxHashMap::default();
    let mut added_protocol_inputs = FxHashSet::default();
    for (instance, protocol_choice) in protocol_choices.iter().enumerate() {
        system.add_input(expr_ctx, *protocol_choice);
        for &symbol in protocol_arg_symbols {
            debug_assert!(matches!(symbols[symbol].kind(), SymbolKind::Arg(_)));
            let input = symbol_bitvec_expr(expr_ctx, symbols, symbol, instance);
            if added_protocol_inputs.insert(input) {
                system.add_input(expr_ctx, input);
            }
            protocol_inputs.insert((instance, symbol), input);
        }
    }

    let core = lower_proto_graph_to_transition_system(
        expr_ctx,
        graph,
        system,
        symbol_to_port,
        port_to_expr,
        symbols,
    );

    LoweredSystemResult {
        ts: core.ts,
        port_to_expr: core.port_to_expr,
        protocol_inputs,
        protocol_choices,
        node_symbol: core.node_symbol,
        done_state: Some(core.done_state),
        external_assert_state: core.external_assert_state,
        internal_assert_state: core.internal_assert_state,
        is_dont_care: core.is_dont_care,
    }
}
