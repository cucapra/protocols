use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph, Transition};
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

/// TODO: Better way to deal with this?
pub fn same_assignment_target(symbols: &SymbolTable, lhs: SymbolId, rhs: SymbolId) -> bool {
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

pub fn guard_assignment(
    protocol: &mut ProtoGraph,
    assignment: Assignment,
    guard: ExprRef,
) -> Assignment {
    let dont_care = protocol.and_guard(guard, assignment.dont_care);
    let concretes = assignment
        .concretes
        .into_iter()
        .filter_map(|(branch_guard, rhs)| {
            let guarded = protocol.and_guard(guard, branch_guard);
            (guarded != protocol.false_id()).then_some((guarded, rhs))
        })
        .collect();

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn concrete_coverage(protocol: &mut ProtoGraph, assignment: &Assignment) -> ExprRef {
    let raw_coverage = assignment
        .concretes
        .iter()
        .fold(protocol.false_id(), |guard, (concrete_guard, _)| {
            protocol.or_guard(guard, *concrete_guard)
        });
    let not_dont_care = protocol.not_guard(assignment.dont_care);
    protocol.and_guard(not_dont_care, raw_coverage)
}

pub fn effective_concretes(
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> Vec<(ExprRef, ExprRef)> {
    let mut prior = assignment.dont_care;
    let mut effective = Vec::with_capacity(assignment.concretes.len());

    for (guard, rhs) in &assignment.concretes {
        let not_prior = protocol.not_guard(prior);
        let effective_guard = protocol.and_guard(not_prior, *guard);
        if effective_guard != protocol.false_id() {
            effective.push((effective_guard, *rhs));
        }
        prior = protocol.or_guard(prior, *guard);
    }

    effective
}

fn coalesce_concretes(
    protocol: &mut ProtoGraph,
    concretes: Vec<(ExprRef, ExprRef)>,
) -> Vec<(ExprRef, ExprRef)> {
    let mut coalesced = Vec::with_capacity(concretes.len());
    for (guard, rhs) in concretes {
        if let Some((existing_guard, existing_rhs)) = coalesced.last_mut()
            && *existing_rhs == rhs
        {
            *existing_guard = protocol.or_guard(*existing_guard, guard);
        } else {
            coalesced.push((guard, rhs));
        }
    }
    coalesced
}

pub fn merge_ordered_assignment(
    protocol: &mut ProtoGraph,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    // Ordered contraction preserves source order: the later action wins over
    // the earlier action. Therefore the new summary's preferences come first.
    let new_concretes = concrete_coverage(protocol, &new);
    let not_new_concretes = protocol.not_guard(new_concretes);
    let old_dont_care = protocol.and_guard(not_new_concretes, existing.dont_care);
    let dont_care = protocol.or_guard(new.dont_care, old_dont_care);

    let mut concretes = new.concretes;
    concretes.extend(existing.concretes);

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn merge_unordered_assignment(
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    let existing_effective = effective_concretes(protocol, &existing);
    let new_effective = effective_concretes(protocol, &new);

    for (existing_guard, existing_rhs) in &existing_effective {
        for (new_guard, new_rhs) in &new_effective {
            // assignments to the same value are totally legal
            if existing_rhs == new_rhs {
                continue;
            }

            // assignments to different concrete values are illegal
            let overlap = protocol.and_guard(*existing_guard, *new_guard);
            if overlap != protocol.false_id() {
                record_internal_assert(protocol, internal_assert_guard, overlap);
            }
        }
    }

    let mut existing_concretes = concrete_coverage(protocol, &existing);
    existing_concretes = protocol.simplifier.simplify(&mut protocol.expr_ctx, existing_concretes);
    let mut new_concretes = concrete_coverage(protocol, &new);
    new_concretes = protocol.simplifier.simplify(&mut protocol.expr_ctx, new_concretes);

    let mut not_new_concretes = protocol.not_guard(new_concretes);
    // not_new_concretes = protocol.simplifier.simplify(&mut protocol.expr_ctx, not_new_concretes);

    let mut existing_dont_care = protocol.and_guard(not_new_concretes, existing.dont_care);
    // existing_dont_care = protocol.simplifier.simplify(&mut protocol.expr_ctx, existing_dont_care);

    let mut not_existing_concretes = protocol.not_guard(existing_concretes);
    // not_existing_concretes = protocol.simplifier.simplify(&mut protocol.expr_ctx, not_existing_concretes);

    let mut new_dont_care = protocol.and_guard(not_existing_concretes, new.dont_care);
    // new_dont_care = protocol.simplifier.simplify(&mut protocol.expr_ctx, new_dont_care);

    let mut dont_care = protocol.or_guard(existing_dont_care, new_dont_care);
    // dont_care = protocol.simplifier.simplify(&mut protocol.expr_ctx, dont_care);
    
    let mut concretes = existing_effective;
    concretes.extend(new_effective);
    let concretes = coalesce_concretes(protocol, concretes);

    Assignment {
        dont_care,
        concretes,
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
        Op::Assign(symbol_id, assignment) => {
            assert_eq!(
                action.guard,
                protocol.true_id(),
                "assignment action guards must be 1; path conditions belong in Assignment"
            );

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

            assert_eq!(
                actions[idx].guard,
                protocol.true_id(),
                "assignment action guards must be 1; path conditions belong in Assignment"
            );
            let existing_assignment = match protocol[actions[idx].op].clone() {
                Op::Assign(_, existing_assignment) => existing_assignment,
                _ => unreachable!(),
            };

            let merged_assignment = if ordered {
                merge_ordered_assignment(protocol, existing_assignment, assignment)
            } else {
                merge_unordered_assignment(
                    protocol,
                    internal_assert_guard,
                    existing_assignment,
                    assignment,
                )
            };

            let new_op = protocol.o(Op::Assign(symbol_id, merged_assignment));
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

pub fn contract_edges(pg: &mut ProtoGraph, symbols: &SymbolTable) {
    contract_edges_from(pg, symbols, pg.entry);
}

/// returns `protocol` with semantic behavior preserved, but no non-step edges
pub fn contract_edges_from(protocol: &mut ProtoGraph, symbols: &SymbolTable, start: NodeId) {
    let node_ids = reachable_node_ids(protocol, start);

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
                let merged_action = match protocol[action.op].clone() {
                    Op::Assign(symbol_id, assignment) => {
                        assert_eq!(
                            action.guard,
                            protocol.true_id(),
                            "assignment action guards must be 1; path conditions belong in Assignment"
                        );
                        let guarded_assignment =
                            guard_assignment(protocol, assignment, incoming_guard);
                        let guarded_op = protocol.o(Op::Assign(symbol_id, guarded_assignment));
                        Action::new(protocol.true_id(), guarded_op)
                    }
                    _ => Action::with_guard(
                        &action,
                        protocol.and_guard(incoming_guard, action.guard),
                    ),
                };
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
    let dut = protocol.dut_sym;
    let input_ports: Vec<SymbolId> = symbols
        .get_children(&dut)
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
            let assignment =
                Assignment::concrete(protocol.false_id(), protocol.true_id(), symbol_expr);
            let op = protocol.o(Op::Assign(symbol_id, assignment));
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

    fn concrete_assignment(protocol: &ProtoGraph, rhs: ExprRef) -> Assignment {
        Assignment::concrete(protocol.false_id(), protocol.true_id(), rhs)
    }

    fn dont_care_assignment(protocol: &ProtoGraph) -> Assignment {
        Assignment::dont_care(protocol.true_id())
    }

    fn expr_str(protocol: &ProtoGraph, expr: ExprRef) -> String {
        protocol.expr_ctx[expr].serialize_to_str(&protocol.expr_ctx)
    }

    #[test]
    fn allows_overlapping_dont_care_and_concrete_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("signal", 1);
        let dont_care = protocol.expr_ctx.bv_symbol("dont_care", 1);
        let concrete = protocol.expr_ctx.bv_symbol("concrete", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let concrete_op = protocol.o(Op::Assign(
            symbol_id,
            concrete_assignment(&protocol, concrete),
        ));
        let dont_care_op = protocol.o(Op::Assign(symbol_id, dont_care_assignment(&protocol)));
        let mut actions = vec![Action::new(protocol.true_id(), concrete_op)];
        let mut internal_assert_guard = None;
        let true_id = protocol.true_id();
        append_action(
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, dont_care_op),
            true,
        );

        // it is perfectly valid to have multiple assignments in an ordered merge
        // i.e. within a single transaction (transactions can change their mind)
        assert!(internal_assert_guard.is_none());

        // the order in which the assigns are given is preserved (Concrete should not subsume DontCare)
        assert_eq!(actions.len(), 1);
        let Op::Assign(_, assignment) = protocol[actions[0].op].clone() else {
            panic!("expected assignment");
        };
        assert_eq!(expr_str(&protocol, assignment.dont_care), "1'b1");
        assert_eq!(assignment.concretes, vec![(protocol.true_id(), concrete)]);
    }

    #[test]
    fn synthesizes_internal_assert_for_overlapping_unordered_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let symbol_id = SymbolId::new(0);
        let symbol = protocol.expr_ctx.bv_symbol("signal", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);

        // Node A: [p] DUT.a := 1
        // Node B: [q] DUT.a := 2
        // Node C: [r] DUT.a := 3
        let p = protocol.expr_ctx.bv_symbol("p", 1);
        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);
        let one = protocol.expr_ctx.bv_symbol("one", 1);
        let two = protocol.expr_ctx.bv_symbol("two", 1);
        let three = protocol.expr_ctx.bv_symbol("three", 1);

        let mut actions = Vec::new();
        let mut internal_assert_guard = None;
        for (guard, rhs) in [(p, one), (q, two), (r, three)] {
            let assignment = Assignment::concrete(protocol.false_id(), guard, rhs);
            let op = protocol.o(Op::Assign(symbol_id, assignment));
            let true_id = protocol.true_id();
            append_action(
                &mut protocol,
                &SymbolTable::default(),
                &mut actions,
                &mut internal_assert_guard,
                Action::new(true_id, op),
                false,
            );
        }

        assert_eq!(actions.len(), 1);
        assert_ne!(actions[0].guard, protocol.false_id());

        // assert any two guards being run together. (p and q) or (p and r)
        assert_eq!(
            expr_str(&protocol, internal_assert_guard.unwrap()),
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

        let q = protocol.expr_ctx.bv_symbol("q", 1);
        let r = protocol.expr_ctx.bv_symbol("r", 1);
        let s = protocol.expr_ctx.bv_symbol("s", 1);

        // Node A: [1] DUT.a := { X if s; 3 if q }
        // Node B: [1] DUT.a := { 4 if r }

        let true_id = protocol.true_id();
        let node_a_op = protocol.o(Op::Assign(
            symbol_id,
            Assignment {
                dont_care: s,
                concretes: vec![(q, three)],
            },
        ));
        let node_b_op = protocol.o(Op::Assign(
            symbol_id,
            Assignment {
                dont_care: protocol.false_id(),
                concretes: vec![(r, four)],
            },
        ));

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

        assert_eq!(actions.len(), 1);
        assert_ne!(actions[0].guard, protocol.false_id());

        // q and r are our concrete assignments to 3 and 4. assignment to 3 only triggers if
        // not s , so there is only a conflicting assignment under ((not s) and q and r)
        assert_eq!(
            expr_str(&protocol, internal_assert_guard.unwrap()),
            "and(and(not(s), q), r)"
        );

        protocol.simplify_all_exprs();

        let Op::Assign(_, assignment) = protocol[actions[0].op].clone() else {
            panic!("expected assignment");
        };

        // Concrete branches from both unordered sides are preferred over DontCare, but the
        // original node-local DontCare still suppresses node A's own concrete branch.
        assert_eq!(expr_str(&protocol, assignment.dont_care), "and(not(r), s)");
        let not_s = protocol.not_guard(s);
        let effective_q = protocol.and_guard(not_s, q);
        assert_eq!(assignment.concretes, vec![(effective_q, three), (r, four)]);
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

        let true_id = protocol.true_id();
        let node_a_op = protocol.o(Op::Assign(
            symbol_id,
            Assignment {
                dont_care: p,
                concretes: vec![(q, three)],
            },
        ));
        let node_b_op = protocol.o(Op::Assign(
            symbol_id,
            Assignment {
                dont_care: protocol.false_id(),
                concretes: vec![(r, three)],
            },
        ));

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

        // any of the forks can trigger: (p or q or r)
        assert_eq!(fork_guard, "or(or(p, q), r)");

        // any two of the forks should not trigger at once
        // below expression is equivalent to (p or q) and (p or r) and (q or r)
        assert_eq!(internal_guard, "or(and(p, q), and(or(p, q), r))");
    }
}
