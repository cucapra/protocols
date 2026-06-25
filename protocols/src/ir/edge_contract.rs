use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph, Transition};
use patronus::expr::ExprRef;

fn symbol_expr(protocol: &mut ProtoGraph, symbols: &SymbolTable, symbol_id: SymbolId) -> ExprRef {
    if let Some(expr) = protocol.symbol_expr(symbol_id) {
        return expr;
    }

    let entry = &symbols[symbol_id];
    let full_name = entry.full_name(symbols);
    let expr = match entry.tpe() {
        FrontType::BitVec(width) => protocol.expr_ctx.bv_symbol(&full_name, width),
        FrontType::Struct(_) | FrontType::Seq(_) | FrontType::UnsignedInt | FrontType::Unknown => {
            panic!(
                "unsupported symbol type {} for {}",
                crate::frontend::serialize::serialize_type(symbols, entry.tpe()),
                full_name
            )
        }
    };
    protocol.cache_symbol_expr(symbol_id, expr);
    expr
}

/// `true` if `rhs` is (after simplification) one of the protocol's don't-care
/// symbols, i.e. an `X` assignment that places no constraint on the pin.
fn is_dont_care(protocol: &mut ProtoGraph, rhs: ExprRef) -> bool {
    let simplified = {
        let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
        simplifier.simplify(expr_ctx, rhs)
    };
    protocol.dont_cares.contains(&simplified)
}

/// Constrain `rhs` to `guard`, falling back to `fallback` outside it. An
/// unconditional (`true`) guard needs no `ite`.
fn lift(protocol: &mut ProtoGraph, guard: ExprRef, rhs: ExprRef, fallback: ExprRef) -> ExprRef {
    if guard == protocol.true_id() {
        rhs
    } else {
        protocol.expr_ctx.ite(guard, rhs, fallback)
    }
}

fn append_action(
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    internal_assert_guard: &mut Option<ExprRef>,
    action: Action,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, rhs) => {
            let default_value = symbol_expr(protocol, symbols, symbol_id);

            // By invariant, there can be at most one existing assignment for this symbol.
            let Some(idx) = actions.iter().position(|prior_action| {
                matches!(protocol[prior_action.op], Op::Assign(prior_symbol_id, _) if prior_symbol_id == symbol_id)
            }) else {
                actions.push(action);
                return;
            };

            let existing_guard = actions[idx].guard;
            let existing_rhs = match protocol[actions[idx].op].clone() {
                Op::Assign(_, existing_rhs) => existing_rhs,
                _ => unreachable!(),
            };
            let (new_guard, new_rhs) = (action.guard, rhs);

            let existing_dc = is_dont_care(protocol, existing_rhs);
            let new_dc = is_dont_care(protocol, new_rhs);

            // A concrete drive is a constraint; a don't-care places none. So
            // whichever side is concrete becomes the outer `ite` selector (it
            // wins wherever it is active, including any guard overlap), and the
            // don't-care only fills the region its own guard covers but the
            // concrete does not. This is independent of which action was
            // appended first.
            let merged_rhs = match (existing_dc, new_dc) {
                // existing concrete wins; new don't-care fills its own region
                (false, true) => {
                    let dc_else = lift(protocol, new_guard, new_rhs, default_value);
                    lift(protocol, existing_guard, existing_rhs, dc_else)
                }
                // new concrete wins; existing don't-care fills its own region
                (true, false) => {
                    let dc_else = lift(protocol, existing_guard, existing_rhs, default_value);
                    lift(protocol, new_guard, new_rhs, dc_else)
                }
                // both don't-care or both concrete: keep the straightforward
                // nesting with the just-appended action outermost
                _ => {
                    let existing_else =
                        lift(protocol, existing_guard, existing_rhs, default_value);
                    lift(protocol, new_guard, new_rhs, existing_else)
                }
            };

            // Two concrete drives that can be simultaneously active with
            // differing values is assert-ed unreachable
            if !existing_dc && !new_dc {
                let overlap = protocol.and_guard(existing_guard, new_guard);
                let equal = protocol.expr_ctx.equal(existing_rhs, new_rhs);
                let disagree = protocol.expr_ctx.not(equal);
                let conflict = protocol.and_guard(overlap, disagree);
                if conflict != protocol.false_id() {
                    *internal_assert_guard = Some(match internal_assert_guard.take() {
                        Some(existing_conflict) => protocol.or_guard(existing_conflict, conflict),
                        None => conflict,
                    });
                }
            }

            let merged_rhs = {
                let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
                simplifier.simplify(expr_ctx, merged_rhs)
            };
            let new_op = protocol.o(Op::Assign(symbol_id, merged_rhs));
            actions[idx].guard = protocol.true_id();
            actions[idx].op = new_op;
        }
        Op::Fork => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Fork))
            {
                let overlap = protocol.and_guard(existing_action.guard, action.guard);
                *internal_assert_guard = Some(match internal_assert_guard.take() {
                    Some(existing_overlap) => protocol.or_guard(existing_overlap, overlap),
                    None => overlap,
                });
                existing_action.guard = protocol.or_guard(existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::Done => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Done))
            {
                existing_action.guard = protocol.or_guard(existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::AssertEq(_, _) => {
            actions.push(action);
        }
        Op::InternalAssertFalse => {
            actions.push(action);
        }
    }
}

/// returns `protocol` with semantic behavior preserved, but no non-step edges
pub fn contract_edges(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    let node_ids = protocol
        .nodes()
        .map(|(node_id, _)| node_id)
        .collect::<Vec<_>>();

    for source_node_id in node_ids.into_iter().rev() {
        let mut contracted_actions = Vec::with_capacity(protocol[source_node_id].actions.len());
        let mut internal_assert_guard = None;
        for action in protocol[source_node_id].actions.clone() {
            append_action(
                protocol,
                symbols,
                &mut contracted_actions,
                &mut internal_assert_guard,
                action,
            );
        }

        let (mut step_transitions, pending_transitions): (Vec<_>, Vec<_>) = protocol
            [source_node_id]
            .transitions
            .clone()
            .into_iter()
            .partition(|transition| transition.consumes_step);

        let mut pending_transitions: VecDeque<_> = pending_transitions
            .into_iter()
            .rev()
            .map(|transition| {
                (transition, {
                    let mut path = BTreeSet::new();
                    path.insert(source_node_id);
                    path
                })
            })
            .collect();

        while let Some((transition, path)) = pending_transitions.pop_front() {
            assert!(!transition.consumes_step);

            let target_node_id = transition.target;
            if path.contains(&target_node_id) {
                internal_assert_guard = Some(match internal_assert_guard.take() {
                    Some(existing_guard) => protocol.or_guard(existing_guard, transition.guard),
                    None => transition.guard,
                });
                continue;
            }

            let incoming_guard = transition.guard;
            let target_actions = protocol[target_node_id].actions.clone();
            let target_transitions = protocol[target_node_id].transitions.clone();
            let mut next_path = path.clone();
            next_path.insert(target_node_id);

            for action in target_actions {
                let merged_action =
                    Action::with_guard(&action, protocol.and_guard(incoming_guard, action.guard));
                append_action(
                    protocol,
                    symbols,
                    &mut contracted_actions,
                    &mut internal_assert_guard,
                    merged_action,
                );
            }

            for target_transition in target_transitions.into_iter().rev() {
                let contracted_transition = Transition::with_guard(
                    &target_transition,
                    protocol.and_guard(incoming_guard, target_transition.guard),
                );
                if contracted_transition.consumes_step {
                    step_transitions.push(contracted_transition);
                } else {
                    pending_transitions.push_back((contracted_transition, next_path.clone()));
                }
            }
        }

        if let Some(internal_assert_guard) = internal_assert_guard {
            let internal_assert_op = protocol.o(Op::InternalAssertFalse);
            let source_node = protocol.node_mut(source_node_id);
            source_node.actions = contracted_actions;
            source_node
                .actions
                .push(Action::new(internal_assert_guard, internal_assert_op));
        } else {
            let source_node = protocol.node_mut(source_node_id);
            source_node.actions = contracted_actions;
        }
        protocol.node_mut(source_node_id).transitions = step_transitions;
    }

    // TODO: check all simplifications here
}

/// returns `protocol` with explicit assignments to every port
/// if a port `DUT.in` is not already assigned, we simply generate `[1] DUT.in := DUT.in;`
pub fn normalize_assignments(protocol: &mut ProtoGraph, symbols: &SymbolTable) {
    let dut = protocol.type_param.expect("protocol has no DUT");
    let input_ports: Vec<SymbolId> = symbols
        .get_children(&dut)
        .into_iter()
        .filter(|sym_id| symbols[*sym_id].is_in_port())
        .collect();

    let node_ids: Vec<NodeId> = protocol.nodes().map(|(node_id, _)| node_id).collect();

    for node_id in node_ids {
        let node_actions = protocol[node_id].actions.clone();

        let assigned_inputs: Vec<SymbolId> = node_actions
            .iter()
            .filter_map(|action| match protocol[action.op] {
                Op::Assign(symbol_id, _) => Some(symbol_id),
                _ => None,
            })
            .collect();

        // unassigned_inputs = input_ports - assigned_inputs
        let unassigned_inputs: Vec<SymbolId> = input_ports
            .iter()
            .copied()
            .filter(|sym_id| !assigned_inputs.contains(sym_id))
            .collect();

        for symbol_id in unassigned_inputs {
            // assign the symbol to its current expression (old value)
            let symbol_expr = symbol_expr(protocol, symbols, symbol_id);
            let op = protocol.o(Op::Assign(symbol_id, symbol_expr));
            protocol.push_action(node_id, Action::new(protocol.true_id(), op))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::ROOT_SCOPE;
    use patronus::expr::SerializableIrNode;

    #[test]
    fn synthesizes_internal_assert_for_overlapping_forks() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);

        let fork1 = protocol.o(Op::Fork);
        let fork2 = protocol.o(Op::Fork);
        let fork3 = protocol.o(Op::Fork);
        protocol.node_mut(protocol.entry).actions = vec![
            Action::new(p, fork1),
            Action::new(q, fork2),
            Action::new(r, fork3),
        ];

        contract_edges(&mut protocol, &SymbolTable::default());

        let actions = &protocol[protocol.entry].actions;
        assert_eq!(actions.len(), 2);
        assert!(matches!(protocol[actions[0].op], Op::Fork));
        assert!(matches!(protocol[actions[1].op], Op::InternalAssertFalse));

        let fork_guard = protocol.expr_ctx[actions[0].guard].serialize_to_str(&protocol.expr_ctx);
        let internal_guard =
            protocol.expr_ctx[actions[1].guard].serialize_to_str(&protocol.expr_ctx);

        // any of the forks can trigger: (p \/ q \/ r)
        assert_eq!(fork_guard, "or(or(p, q), r)");

        // any two of the forks should not trigger at once
        // below expression is equivalent to (p \/ q) /\ (p \/ r) /\ (q \/ r)
        assert_eq!(internal_guard, "or(and(p, q), and(or(p, q), r))");
    }
}
