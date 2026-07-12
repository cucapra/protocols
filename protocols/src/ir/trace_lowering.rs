// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use baa::BitVecValue;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

use crate::Value;
use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::edge_contract::{append_action, contract_edges, guard_assignment};
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer, TraceArgSubst};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph, Transition};
use patronus::expr::Context as ExprContext;

impl<'a> Lowerer<'a> {
    /// Build the per-copy argument substitution and lower one transaction body.
    fn lower_transaction(
        &mut self,
        ast: &Protocol,
        values: &[Value],
        keep_done: bool,
    ) -> LoweredFragmentInfo {
        assert_eq!(
            ast.args.len(),
            values.len(),
            "argument count mismatch for protocol {}",
            ast.name
        );
        let mut subst = TraceArgSubst::default();
        for (arg, value) in ast.args.iter().zip(values) {
            let bvv: BitVecValue = value
                .clone()
                .try_into()
                .unwrap_or_else(|_| panic!("unsupported argument type for {}", ast.name));
            let lit = self.ir.expr_ctx.bv_lit(&bvv);
            subst.insert(arg.symbol(), lit);
        }

        // set the arg substitution to the current transaction's args
        self.trace_arg_subst = subst;
        self.lower_protocol_fragment(ast, keep_done)
    }

    /// Merge a contracted entry node directly into a graft_points node using an unordered node merge.
    pub fn graft_contracted_entry(
        &mut self,
        graft_points_node_id: NodeId,
        entry_node_id: NodeId,
        graft_guard: ExprRef,
    ) {
        let mut actions = self.ir[graft_points_node_id].actions.clone();
        let entry_actions = self.ir[entry_node_id].actions.clone();
        let mut internal_assert_guard = None;

        for action in entry_actions {
            let guarded_action = match self.ir[action.op].clone() {
                Op::Assign(symbol_id, assignment) => {
                    assert_eq!(
                        action.guard,
                        self.ir.true_id(),
                        "assignment action guards must be 1; path conditions belong in Assignment"
                    );
                    let guarded_assignment =
                        guard_assignment(&mut self.ir, assignment, graft_guard);
                    let guarded_op = self.ir.o(Op::Assign(symbol_id, guarded_assignment));
                    Action::new(self.ir.true_id(), guarded_op)
                }
                _ => {
                    let guard = self.ir.and_guard(graft_guard, action.guard);
                    action.with_guard(guard)
                }
            };
            append_action(
                &mut self.ir,
                self.symbols,
                &mut actions,
                &mut internal_assert_guard,
                guarded_action,
                false,
            );
        }

        if let Some(internal_assert_guard) = internal_assert_guard {
            let internal_assert_op = self.ir.o(Op::InternalAssertFalse);
            actions.push(Action::new(internal_assert_guard, internal_assert_op));
        }

        let mut transitions = self.ir[graft_points_node_id].transitions.clone();
        for transition in self.ir[entry_node_id].transitions.clone() {
            let guard = self.ir.and_guard(graft_guard, transition.guard);
            transitions.push(transition.with_guard(guard));
        }

        let graft_points_node = self.ir.node_mut(graft_points_node_id);
        graft_points_node.actions = actions;
        graft_points_node.transitions = transitions;
    }

    /// Take the first trace of the remaining transactions, lower it, contract it, and then merge it into the IR by merging the entry node with each graft point of the previous transaction. Recurse with the remaining traces.
    fn append_trace_transactions(
        &mut self,
        graft_points: Vec<(NodeId, ExprRef)>,
        remaining: &[(String, Vec<Value>)],
        protos_by_name: &FxHashMap<&str, &Protocol>,
    ) {
        let Some(((name, values), rest)) = remaining.split_first() else {
            return;
        };

        if graft_points.is_empty() {
            panic!(
                "{} transaction(s) remain in the trace but the previous transaction \
                 exposed no fork points to graft onto",
                remaining.len()
            );
        }

        let ast = *protos_by_name
            .get(name.as_str())
            .unwrap_or_else(|| panic!("unknown protocol {name}"));
        let keep_done = rest.is_empty();

        let fragment = self.lower_transaction(ast, values, keep_done);

        // TODO: we're applying these passes to the entire IR, but technically
        // this is a bit wasteful since we only need to postprocess this
        // disconnected fragment before grafting it into the trace graph.
        self.postprocess_trace_fragment(&fragment);
        let next = self.graft_points(&fragment);

        for (node, guard) in graft_points {
            self.graft_contracted_entry(node, fragment.entry, guard);
        }
        contract_edges(&mut self.ir, self.symbols);

        self.append_trace_transactions(next, rest, protos_by_name);
    }
}

/// Lower a whole trace of known transactions into a single joint `ProtoGraph`.
/// The first transaction becomes the graph entry and each later transaction is
/// grafted onto the previous transaction's fork graft_points.
pub fn lower_trace_to_ir(
    trace: &[(String, Vec<Value>)],
    protos_by_name: &FxHashMap<&str, &Protocol>,
    symbols: &SymbolTable,
    expr_ctx: ExprContext,
) -> ProtoGraph {
    assert!(!trace.is_empty(), "cannot lower an empty trace");

    let (first_name, first_values) = &trace[0];
    let first_ast = *protos_by_name
        .get(first_name.as_str())
        .unwrap_or_else(|| panic!("unknown protocol {first_name}"));

    // set up the lowerer and lower the initial transaction
    let mut lowerer = Lowerer::with_expr_ctx(first_ast.ctx.clone(), symbols, expr_ctx);
    let first = lowerer.lower_transaction(first_ast, first_values, trace.len() == 1);
    let entry_node = lowerer.ir.entry;
    let true_id = lowerer.ir.true_id();
    lowerer
        .ir
        .push_transition(entry_node, Transition::new(true_id, first.entry, false));
    lowerer.postprocess_trace_fragment(&first);
    contract_edges(&mut lowerer.ir, symbols);

    // pass in the initial IR with the first transaction and its graft points, and append_trace_transactions will lower the rest of the trace from here.
    let graft_points = lowerer.graft_points(&first);
    lowerer.append_trace_transactions(graft_points, &trace[1..], protos_by_name);
    lowerer.ir.simplify_all_exprs();
    lowerer.ir
}
