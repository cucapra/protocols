use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph, Transition};
use patronus::expr::{Expr, ExprRef};

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

/// Constrain `rhs` to `guard`, falling back to `fallback` outside it. An
/// unconditional (`true`) guard needs no `ite`.
fn lift(protocol: &mut ProtoGraph, guard: ExprRef, rhs: ExprRef, fallback: ExprRef) -> ExprRef {
    if guard == protocol.true_id() {
        rhs
    } else {
        protocol.expr_ctx.ite(guard, rhs, fallback)
    }
}

fn same_assignment_target(symbols: &SymbolTable, lhs: SymbolId, rhs: SymbolId) -> bool {
    lhs == rhs || symbols[lhs].full_name(symbols) == symbols[rhs].full_name(symbols)
}

fn record_internal_assert(
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    guard: ExprRef,
) {
    *internal_assert_guard = Some(match internal_assert_guard.take() {
        Some(existing_guard) => protocol.or_guard(existing_guard, guard),
        None => guard,
    });
}

#[derive(Clone, Copy)]
struct AssignmentBranch {
    guard: ExprRef,
    rhs: ExprRef,
    is_dont_care: bool,
}

fn simplify_expr(protocol: &mut ProtoGraph, expr: ExprRef) -> ExprRef {
    let (expr_ctx, simplifier) = (&mut protocol.expr_ctx, &mut protocol.simplifier);
    simplifier.simplify(expr_ctx, expr)
}

fn push_assignment_branch(
    protocol: &mut ProtoGraph,
    branches: &mut Vec<AssignmentBranch>,
    guard: ExprRef,
    rhs: ExprRef,
) {
    let guard = simplify_expr(protocol, guard);
    if guard == protocol.false_id() {
        return;
    }

    let rhs = simplify_expr(protocol, rhs);
    branches.push(AssignmentBranch {
        guard,
        rhs,
        is_dont_care: protocol.dont_cares.contains(&rhs),
    });
}

fn flatten_assignment_rhs(
    protocol: &mut ProtoGraph,
    rhs: ExprRef,
    default_value: ExprRef,
    action_guard: ExprRef,
) -> Vec<AssignmentBranch> {
    let mut branches = Vec::new();
    let mut path_guard = simplify_expr(protocol, action_guard);
    let mut cursor = simplify_expr(protocol, rhs);

    while path_guard != protocol.false_id() && cursor != default_value {
        match protocol.expr_ctx[cursor].clone() {
            Expr::BVIte { cond, tru, fals } => {
                let branch_guard = protocol.and_guard(path_guard, cond);
                push_assignment_branch(protocol, &mut branches, branch_guard, tru);

                let not_cond = protocol.not_guard(cond);
                path_guard = protocol.and_guard(path_guard, not_cond);
                cursor = simplify_expr(protocol, fals);
            }
            _ => {
                push_assignment_branch(protocol, &mut branches, path_guard, cursor);
                break;
            }
        }
    }

    branches
}

fn rebuild_assignment_rhs(
    protocol: &mut ProtoGraph,
    branches: &[AssignmentBranch],
    default_value: ExprRef,
) -> ExprRef {
    branches
        .iter()
        .rev()
        .fold(default_value, |fallback, branch| {
            lift(protocol, branch.guard, branch.rhs, fallback)
        })
}

fn append_assignment_branches(
    output: &mut Vec<AssignmentBranch>,
    branches: &[AssignmentBranch],
    dont_care: bool,
) {
    output.extend(
        branches
            .iter()
            .copied()
            .filter(|branch| branch.is_dont_care == dont_care),
    );
}

fn merge_unordered_assignment_rhs(
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    default_value: ExprRef,
    existing_guard: ExprRef,
    existing_rhs: ExprRef,
    new_guard: ExprRef,
    new_rhs: ExprRef,
) -> ExprRef {
    let existing_branches =
        flatten_assignment_rhs(protocol, existing_rhs, default_value, existing_guard);
    let new_branches = flatten_assignment_rhs(protocol, new_rhs, default_value, new_guard);

    for existing_branch in existing_branches
        .iter()
        .filter(|branch| !branch.is_dont_care)
    {
        for new_branch in new_branches.iter().filter(|branch| !branch.is_dont_care) {
            if existing_branch.rhs == new_branch.rhs {
                continue;
            }

            let overlap = protocol.and_guard(existing_branch.guard, new_branch.guard);
            if overlap != protocol.false_id() {
                record_internal_assert(protocol, internal_assert_guard, overlap);
            }
        }
    }

    let mut merged_branches = Vec::with_capacity(existing_branches.len() + new_branches.len());
    append_assignment_branches(&mut merged_branches, &existing_branches, false);
    append_assignment_branches(&mut merged_branches, &new_branches, false);
    append_assignment_branches(&mut merged_branches, &existing_branches, true);
    append_assignment_branches(&mut merged_branches, &new_branches, true);

    rebuild_assignment_rhs(protocol, &merged_branches, default_value)
}

fn merge_assignment_rhs(
    protocol: &mut ProtoGraph,
    ordered: bool,
    internal_assert_guard: &mut Option<ExprRef>,
    default_value: ExprRef,
    existing_guard: ExprRef,
    existing_rhs: ExprRef,
    new_guard: ExprRef,
    new_rhs: ExprRef,
) -> ExprRef {
    if ordered {
        let existing_else = lift(protocol, existing_guard, existing_rhs, default_value);
        lift(protocol, new_guard, new_rhs, existing_else)
    } else {
        merge_unordered_assignment_rhs(
            protocol,
            internal_assert_guard,
            default_value,
            existing_guard,
            existing_rhs,
            new_guard,
            new_rhs,
        )
    }
}

pub fn append_action(
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    internal_assert_guard: &mut Option<ExprRef>,
    action: Action,
    ordered: bool,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, rhs) => {
            let default_value = symbol_expr(protocol, symbols, symbol_id);

            // By invariant, there can be at most one existing assignment for this symbol.
            let Some(idx) = actions.iter().position(|prior_action| {
                matches!(
                    protocol[prior_action.op],
                    Op::Assign(prior_symbol_id, _)
                        if same_assignment_target(symbols, prior_symbol_id, symbol_id)
                )
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

            let merged_rhs = merge_assignment_rhs(
                protocol,
                ordered,
                internal_assert_guard,
                default_value,
                existing_guard,
                existing_rhs,
                new_guard,
                new_rhs,
            );

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
                record_internal_assert(protocol, internal_assert_guard, overlap);
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
                true,
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
                    true,
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
    use cranelift_entity::EntityRef;
    use patronus::expr::SerializableIrNode;

    #[test]
    fn allows_overlapping_dont_care_and_concrete_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("signal", 1);
        let dont_care = protocol.expr_ctx.bv_symbol("dont_care", 1);
        let concrete = protocol.expr_ctx.bv_symbol("concrete", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let dont_care_op = protocol.o(Op::Assign(symbol_id, dont_care));
        let concrete_op = protocol.o(Op::Assign(symbol_id, concrete));
        let mut actions = vec![Action::new(protocol.true_id(), dont_care_op)];
        let mut internal_assert_guard = None;
        let true_id = protocol.true_id();
        append_action(
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, concrete_op),
            false,
        );

        assert!(internal_assert_guard.is_none());
    }

    #[test]
    fn synthesizes_internal_assert_for_overlapping_unordered_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("signal", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);

        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);
        let one = protocol.expr_ctx.bv_symbol("one", 1);
        let two = protocol.expr_ctx.bv_symbol("two", 1);
        let three = protocol.expr_ctx.bv_symbol("three", 1);

        let mut actions = Vec::new();
        let mut internal_assert_guard = None;
        for (guard, rhs) in [(p, one), (q, two), (r, three)] {
            let op = protocol.o(Op::Assign(symbol_id, rhs));
            append_action(
                &mut protocol,
                &SymbolTable::default(),
                &mut actions,
                &mut internal_assert_guard,
                Action::new(guard, op),
                false,
            );
        }

        assert_eq!(actions.len(), 1);
        assert_eq!(
            protocol.expr_ctx[actions[0].guard].serialize_to_str(&protocol.expr_ctx),
            "1'b1"
        );
        assert_eq!(
            protocol.expr_ctx[internal_assert_guard.unwrap()].serialize_to_str(&protocol.expr_ctx),
            "or(or(and(p, q), and(p, r)), and(and(not(p), q), r))"
        );
    }

    #[test]
    fn unordered_assignment_merge_preserves_ordered_ite_precedence() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("DUT.a", 1);
        let dont_care = protocol.expr_ctx.bv_symbol("dont_care", 1);
        let three = protocol.expr_ctx.bv_symbol("three", 1);
        let four = protocol.expr_ctx.bv_symbol("four", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);
        let s = protocol.expr_ctx.bv_symbol("s", 1);

        let q_three = protocol.expr_ctx.ite(q, three, symbol);
        let node_a_rhs = protocol.expr_ctx.ite(p, dont_care, q_three);
        let node_b_rhs = protocol.expr_ctx.ite(r, four, symbol);
        let node_c_rhs = protocol.expr_ctx.ite(s, dont_care, symbol);
        let true_id = protocol.true_id();
        let node_a_op = protocol.o(Op::Assign(symbol_id, node_a_rhs));
        let node_b_op = protocol.o(Op::Assign(symbol_id, node_b_rhs));
        let node_c_op = protocol.o(Op::Assign(symbol_id, node_c_rhs));

        let mut actions = vec![Action::new(true_id, node_a_op)];
        let mut internal_assert_guard = None;

        append_action(
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, node_b_op),
            false,
        );
        append_action(
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, node_c_op),
            false,
        );

        assert_eq!(actions.len(), 1);
        assert_eq!(
            protocol.expr_ctx[actions[0].guard].serialize_to_str(&protocol.expr_ctx),
            "1'b1"
        );
        assert_eq!(
            protocol.expr_ctx[internal_assert_guard.unwrap()].serialize_to_str(&protocol.expr_ctx),
            "and(and(not(p), q), r)"
        );

        let Op::Assign(_, rhs) = protocol[actions[0].op] else {
            panic!("expected assignment");
        };
        assert_eq!(
            protocol.expr_ctx[rhs].serialize_to_str(&protocol.expr_ctx),
            "ite(and(not(p), q), three, ite(and(not(and(not(p), q)), r), four, ite(and(not(or(and(not(p), q), r)), p), dont_care, ite(s, dont_care, DUT.a))))"
        );
    }

    #[test]
    fn unordered_assignment_merge_allows_overlapping_equal_concretes() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("DUT.a", 1);
        let dont_care = protocol.expr_ctx.bv_symbol("dont_care", 1);
        let three = protocol.expr_ctx.bv_symbol("three", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);

        let q_three = protocol.expr_ctx.ite(q, three, symbol);
        let node_a_rhs = protocol.expr_ctx.ite(p, dont_care, q_three);
        let node_b_rhs = protocol.expr_ctx.ite(r, three, symbol);
        let true_id = protocol.true_id();
        let node_a_op = protocol.o(Op::Assign(symbol_id, node_a_rhs));
        let node_b_op = protocol.o(Op::Assign(symbol_id, node_b_rhs));

        let mut actions = vec![Action::new(true_id, node_a_op)];
        let mut internal_assert_guard = None;

        append_action(
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, node_b_op),
            false,
        );

        assert!(internal_assert_guard.is_none());
    }

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
