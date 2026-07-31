use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::bounded_lowering::{graft_choice_entries_into, mark_graft_point_ready};
use crate::ir::edge_contract::contract_edges;
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph, Transition};
use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

/// Lower a set of protocols to a joint IR that represents traces of any length
/// Precondition: every `p \in protos` must fork in its exit node (there is no possibility of
/// overlapping protcols)
pub fn lower_steady_state(
    protos: Vec<Protocol>,
    symbols: &SymbolTable,
    mut expr_ctx: ExprContext,
) -> (ProtoGraph, ExprRef) {
    assert!(!protos.is_empty());
    let num_protos = protos.len();
    let width = if num_protos <= 1 {
        1
    } else {
        usize::BITS - (num_protos - 1).leading_zeros()
    };
    let proto_choice: ExprRef = expr_ctx.bv_symbol(&"proto_choice".to_string(), width);

    let first_ast = protos.first().unwrap();
    let mut graft_points: Vec<(NodeId, ExprRef)> = vec![];

    // set up the lowerer and lower all the protocols
    let mut lowerer = Lowerer::with_expr_ctx(first_ast.ctx.clone(), symbols, expr_ctx);
    // TODO: Handle done vs not done
    let mut lowered_protocols: Vec<LoweredFragmentInfo> = vec![];
    for protocol in protos {
        let mut pg = lowerer.lower_protocol_fragment(&protocol, false, true);
        // lowerer.postprocess_trace_fragment(&pg);
        pg.graft_points = lowerer.graft_points(&pg);
        lowered_protocols.push(pg);
    }

    let arg_symbols: Vec<SymbolId> = lowerer
        .symbols
        .get_args()
        .into_iter()
        .filter(|symbol_id| {
            matches!(lowerer.symbols[*symbol_id].kind(), SymbolKind::Arg(_))
                && lowerer.ir.symbol_expr(*symbol_id).is_some()
        })
        .collect();

    // TODO: kinda janky way to make an identity instance substitution
    let instance_substitutions: FxHashMap<ExprRef, ExprRef> = arg_symbols
        .iter()
        .filter_map(|symbol_id| lowerer.ir.symbol_expr(*symbol_id).map(|expr| (expr, expr)))
        .collect();

    let entry_node = lowerer.ir.entry;

    let mut initial_choices = Vec::with_capacity(num_protos);
    for (idx, prototype) in lowered_protocols.iter().enumerate().take(num_protos) {
        let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(idx, width);
        let node_equals = if idx + 1 == num_protos {
            lowerer
                .ir
                .expr_ctx
                .greater_or_equal(proto_choice, proto_idx_expr)
        } else {
            lowerer.ir.expr_ctx.equal(proto_choice, proto_idx_expr)
        };
        let new_frag = lowerer.copy_protocol_fragment(prototype.clone(), &instance_substitutions);

        // TODO: all exits have the done action. If these were interpreter, the graph interpreter would actually get mad at this,
        // but it shouldn't. Done doesn't really have meaning for driver automata, just for monitors.
        let done_op = lowerer.ir.o(Op::Done);
        let true_id = lowerer.ir.true_id();
        lowerer
            .ir
            .push_action(new_frag.exit, Action::new(true_id, done_op));

        for &(node, guard) in &new_frag.graft_points {
            mark_graft_point_ready(&mut lowerer, node, guard);
        }
        graft_points.extend(new_frag.graft_points.clone());
        initial_choices.push((new_frag.entry, node_equals));
    }
    graft_choice_entries_into(&mut lowerer, entry_node, initial_choices);

    // contract_edges(&mut lowerer.ir, lowerer.symbols);

    // pass in the initial IR with and its graft points, and append_trace_transactions will lower the rest of the trace from here.
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, proto_choice)
}
