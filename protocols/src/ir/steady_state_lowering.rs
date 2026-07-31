use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::ir::bounded_lowering::graft_choice_entries_into;
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use patronus::expr::{Context as ExprContext, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

fn loop_exit_to_entry(lowerer: &mut Lowerer<'_>, fragment: &LoweredFragmentInfo, entry: NodeId) {
    for node in fragment.nodes.iter().copied() {
        if node == fragment.exit {
            continue;
        }

        for transition in &mut lowerer.ir.node_mut(node).transitions {
            if transition.target == fragment.exit {
                transition.target = entry;
                transition.consumes_step = true;
            }
        }
    }
}

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

    // The steady-state automaton has one reusable transaction slot. Use the
    // same #0 argument names that `into_bmc_transition_system` creates for its
    // first slot so the copied graph reads those transition-system inputs.
    let instance_substitutions: FxHashMap<ExprRef, ExprRef> = arg_symbols
        .iter()
        .filter_map(|symbol_id| {
            let old_expr = lowerer.ir.symbol_expr(*symbol_id)?;
            let width = old_expr.get_bv_type(&lowerer.ir.expr_ctx)?;
            let name = lowerer.symbols.full_name_from_symbol_id(symbol_id);
            let slot_expr = lowerer.ir.expr_ctx.bv_symbol(&format!("{name}#0"), width);
            Some((old_expr, slot_expr))
        })
        .collect();

    let entry_node = lowerer.ir.entry;
    // the entry node is a fork point (where we start new transactions)
    let fork_op = lowerer.ir.o(Op::Fork);
    lowerer
        .ir
        .push_action(entry_node, Action::new(lowerer.ir.true_id(), fork_op));

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

        initial_choices.push((new_frag.entry, node_equals));

        loop_exit_to_entry(&mut lowerer, &new_frag, entry_node);
    }
    graft_choice_entries_into(&mut lowerer, entry_node, initial_choices);

    // contract_edges(&mut lowerer.ir, lowerer.symbols);

    // pass in the initial IR with and its graft points, and append_trace_transactions will lower the rest of the trace from here.
    lowerer.ir.simplify_all_exprs();
    (lowerer.ir, proto_choice)
}
