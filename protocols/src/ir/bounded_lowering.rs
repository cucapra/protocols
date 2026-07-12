use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolKind, SymbolTable};
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

fn mark_graft_point_ready(lowerer: &mut Lowerer<'_>, node: NodeId, guard: ExprRef) {
    let already_ready = lowerer.ir[node]
        .actions
        .iter()
        .any(|action| matches!(lowerer.ir[action.op], Op::Fork));
    if !already_ready {
        let fork_op = lowerer.ir.o(Op::Fork);
        lowerer.ir.push_action(node, Action::new(guard, fork_op));
    }
}

/// Lower a set of protocols to a joint IR that represents any trace up to `k` in length
pub fn lower_bmc(
    protos: Vec<Protocol>,
    symbols: &SymbolTable,
    mut expr_ctx: ExprContext,
    bound: usize,
) -> (ProtoGraph, Vec<ExprRef>) {
    assert!(!protos.is_empty());
    let num_protos = protos.len();
    let width = if num_protos <= 1 {
        1
    } else {
        usize::BITS - (num_protos - 1).leading_zeros()
    };
    let proto_choices: Vec<ExprRef> = (0..bound)
        .map(|slot| expr_ctx.bv_symbol(&format!("proto_choice_{slot}"), width))
        .collect();

    let first_ast = protos.first().unwrap();
    let mut graft_points: Vec<(NodeId, ExprRef)> = vec![];

    // set up the lowerer and lower the initial transaction
    let mut lowerer = Lowerer::with_expr_ctx(first_ast.ctx.clone(), symbols, expr_ctx);
    // TODO: Handle done vs not done
    let mut lowered_protocols: Vec<LoweredFragmentInfo> = vec![];
    for protocol in protos {
        let pg = lowerer.lower_protocol_fragment(&protocol, false);
        lowerer.postprocess_trace_fragment(&pg);
        lowered_protocols.push(pg);
    }

    let arg_symbols: Vec<_> = lowerer
        .symbols
        .get_args()
        .into_iter()
        .filter(|symbol_id| {
            matches!(lowerer.symbols[*symbol_id].kind(), SymbolKind::Arg(_))
                && lowerer.ir.symbol_expr(*symbol_id).is_some()
        })
        .collect();

    let instance_substitutions: Vec<FxHashMap<ExprRef, ExprRef>> = (0..bound)
        .map(|slot| {
            arg_symbols
                .iter()
                .filter_map(|symbol_id| {
                    let old_expr = lowerer.ir.symbol_expr(*symbol_id)?;
                    let width = old_expr.get_bv_type(&lowerer.ir.expr_ctx)?;
                    let name = lowerer.symbols.full_name_from_symbol_id(symbol_id);
                    let new_expr = lowerer
                        .ir
                        .expr_ctx
                        .bv_symbol(&format!("{name}#{slot}"), width);
                    Some((old_expr, new_expr))
                })
                .collect()
        })
        .collect();

    let entry_node = lowerer.ir.entry;

    let mut initial_choices = Vec::with_capacity(num_protos);
    for idx in 0..num_protos {
        let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(idx, width);
        let node_equals = if idx + 1 == num_protos {
            lowerer
                .ir
                .expr_ctx
                .greater_or_equal(proto_choices[0], proto_idx_expr)
        } else {
            lowerer.ir.expr_ctx.equal(proto_choices[0], proto_idx_expr)
        };
        let prototype = lowered_protocols[idx].clone();
        let new_frag = lowerer.copy_protocol_fragment(prototype, &instance_substitutions[0]);

        // if bound is 1, then exit should have the done action
        if bound == 1 {
            let done_op = lowerer.ir.o(Op::Done);
            let true_id = lowerer.ir.true_id();
            lowerer
                .ir
                .push_action(new_frag.exit, Action::new(true_id, done_op));
        }

        for &(node, guard) in &new_frag.graft_points {
            mark_graft_point_ready(&mut lowerer, node, guard);
        }
        graft_points.extend(new_frag.graft_points.clone());
        initial_choices.push((new_frag.entry, node_equals));
    }
    // lowerer.graft_choice_entries(entry_node, initial_choices);
    for (node, guard) in initial_choices {
        lowerer.graft_contracted_entry(entry_node, node, guard);
    }

    let mut next_graft_points: Vec<(NodeId, ExprRef)> = vec![];

    // do the next (bound-1) lowerings
    for i in 1..bound {
        // TODO: the variable naming here sucks
        while let Some((graft_node, guard)) = graft_points.pop() {
            let mut choices = Vec::with_capacity(num_protos);
            for idx in 0..num_protos {
                // The final protocol absorbs the selector tail.
                let proto_idx_expr = lowerer.ir.expr_ctx.bit_vec_val(idx, width);
                let node_equals = if idx + 1 == num_protos {
                    lowerer
                        .ir
                        .expr_ctx
                        .greater_or_equal(proto_choices[i], proto_idx_expr)
                } else {
                    lowerer.ir.expr_ctx.equal(proto_choices[i], proto_idx_expr)
                };
                let and_guard = lowerer.ir.and_guard(guard, node_equals);

                let prototype = lowered_protocols[idx].clone();
                let new_frag =
                    lowerer.copy_protocol_fragment(prototype, &instance_substitutions[i]);

                // if we're at the last transaction, then exit should have the done action
                if i == bound - 1 {
                    let done_op = lowerer.ir.o(Op::Done);
                    let true_id = lowerer.ir.true_id();
                    lowerer
                        .ir
                        .push_action(new_frag.exit, Action::new(true_id, done_op));
                }

                for &(graft_node, graft_guard) in &new_frag.graft_points {
                    mark_graft_point_ready(&mut lowerer, graft_node, graft_guard);
                }
                next_graft_points.extend(new_frag.graft_points.clone());
                choices.push((new_frag.entry, and_guard));
            }
            // lowerer.graft_choice_entries(node, choices);
            for (node, guard) in choices {
                lowerer.graft_contracted_entry(graft_node, node, guard);
            }
        }

        // refill with the new set of graft points
        graft_points.extend(std::mem::take(&mut next_graft_points));
    }

    // pass in the initial IR with and its graft points, and append_trace_transactions will lower the rest of the trace from here.
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, proto_choices)
}
