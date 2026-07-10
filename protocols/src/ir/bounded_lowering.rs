use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::lowering::Lowerer;
use crate::ir::proto_graph::{NodeId, ProtoGraph, Transition};
use patronus::expr::{Context as ExprContext, ExprRef};

/// Lower a set of protocols to a joint IR that represents any trace up to `k` in length
pub fn lower_bmc(
    protos: Vec<Protocol>,
    symbols: &SymbolTable,
    mut expr_ctx: ExprContext,
    bound: usize,
) -> (ProtoGraph, ExprRef) {
    assert!(!protos.is_empty());
    let width = usize::BITS - protos.len().leading_zeros();
    let proto_choice = expr_ctx.bv_symbol("proto_choice", width);

    let first_ast = protos.get(0).unwrap();
    let mut graft_points: Vec<(NodeId, ExprRef)> = vec![];

    // set up the lowerer and lower the initial transaction
    let mut lowerer = Lowerer::with_expr_ctx(first_ast.ctx.clone(), symbols, expr_ctx);
    let first = lowerer.lower_protocol_fragment(first_ast, bound == 1);
    lowerer.postprocess_trace_fragment(&first);

    let entry_node = lowerer.ir.entry;
    let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(0, width);
    let node_equals = lowerer.ir.expr_ctx.equal(proto_choice, proto_idx_expr);
    graft_points.extend(
        lowerer
            .graft_points(&first)
            .into_iter()
            .map(|(node, guard)| (node, lowerer.ir.expr_ctx.and(guard, node_equals))),
    );
    lowerer.graft_contracted_entry(entry_node, first.entry, node_equals);

    // do the same with the rest of the protocols
    for (proto_idx, protocol) in protos[1..].iter().enumerate() {
        let lowered_proto = lowerer.lower_protocol_fragment(protocol, bound == 1);
        lowerer.postprocess_trace_fragment(&lowered_proto);

        let proto_idx = proto_idx + 1;
        let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(proto_idx, width);
        let node_equals = lowerer.ir.expr_ctx.equal(proto_choice, proto_idx_expr);
        graft_points.extend(
            lowerer
                .graft_points(&lowered_proto)
                .into_iter()
                .map(|(node, guard)| (node, lowerer.ir.expr_ctx.and(guard, node_equals))),
        );
        lowerer.graft_contracted_entry(entry_node, lowered_proto.entry, node_equals)
    }

    let mut next_graft_points: Vec<(NodeId, ExprRef)> = vec![];

    // do the next (bound-1) lowerings
    for i in 1..bound {
        println!("{}", i);
        println!("{}", graft_points.len());
        while let Some((node, guard)) = graft_points.pop() {
            for (proto_idx, protocol) in protos.iter().enumerate() {
                // fork if `guard AND proto_choice == proto_idx
                let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(proto_idx, width);
                let node_equals = lowerer.ir.expr_ctx.equal(proto_choice, proto_idx_expr);
                let and_guard = lowerer.ir.expr_ctx.and(guard, node_equals);

                let lowered_proto = lowerer.lower_protocol_fragment(protocol, i + 1 == bound);
                lowerer.postprocess_trace_fragment(&lowered_proto);
                // println!("postprocess");
                let fragment_graft_points = lowerer
                    .graft_points(&lowered_proto)
                    .into_iter()
                    .map(|(next_node, next_guard)| {
                        (next_node, lowerer.ir.expr_ctx.and(and_guard, next_guard))
                    })
                    .collect::<Vec<_>>();

                lowerer.graft_contracted_entry(node, lowered_proto.entry, and_guard);

                next_graft_points.extend(fragment_graft_points);
            }
        }

        // refill with the new set of graft points
        graft_points.extend(std::mem::take(&mut next_graft_points));
    }

    // pass in the initial IR with and its graft points, and append_trace_transactions will lower the rest of the trace from here.
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, proto_choice)
}
