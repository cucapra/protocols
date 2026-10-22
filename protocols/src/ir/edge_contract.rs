use std::collections::{BTreeSet, VecDeque};

use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type as FrontType};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, remap_expr
};
use patronus::expr::{Context, ExprRef};
use rustc_hash::FxHashMap;

fn symbol_expr(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    symbol_id: SymbolId,
) -> ExprRef {
    if let Some(expr) = protocol.symbol_expr(symbol_id) {
        return expr;
    }

    let entry = &symbols[symbol_id];
    let full_name = entry.full_name(symbols);
    let expr = match entry.tpe() {
        FrontType::BitVec(width) => ctx.bv_symbol(&full_name, width),
        FrontType::Struct(_)
        | FrontType::Seq(_)
        | FrontType::Tuple(_)
        | FrontType::UnsignedInt
        | FrontType::Unknown => {
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
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    guard: ExprRef,
) {
    *internal_assert_guard = Some(match internal_assert_guard.take() {
        Some(existing_guard) => protocol.or_guard(ctx, existing_guard, guard),
        None => guard,
    });
}

pub fn guard_assignment(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: Assignment,
    guard: ExprRef,
) -> Assignment {
    let dont_care = protocol.and_guard(ctx, guard, assignment.dont_care);
    let concretes = assignment
        .concretes
        .into_iter()
        .filter_map(|(branch_guard, rhs)| {
            let guarded = protocol.and_guard(ctx, guard, branch_guard);
            (guarded != ctx.get_false()).then_some((guarded, rhs))
        })
        .collect();

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn guard_disjoint_assignment(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: Assignment,
    guard: ExprRef,
) -> Assignment {
    let not_dont_care = protocol.not_guard(ctx, assignment.dont_care);
    let dont_care = protocol.and_guard(ctx, guard, assignment.dont_care);
    let concretes = assignment
        .concretes
        .into_iter()
        .filter_map(|(branch_guard, rhs)| {
            let branch_guard = protocol.and_guard(ctx, not_dont_care, branch_guard);
            let guarded = protocol.and_guard(ctx, guard, branch_guard);
            (guarded != ctx.get_false()).then_some((guarded, rhs))
        })
        .collect();

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn concrete_coverage(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> ExprRef {
    let raw_coverage = assignment
        .concretes
        .iter()
        .fold(ctx.get_false(), |guard, (concrete_guard, _)| {
            protocol.or_guard(ctx, guard, *concrete_guard)
        });
    let not_dont_care = protocol.not_guard(ctx, assignment.dont_care);
    protocol.and_guard(ctx, not_dont_care, raw_coverage)
}

fn effective_concretes(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> Vec<(ExprRef, ExprRef)> {
    let mut prior = assignment.dont_care;
    let mut effective = Vec::with_capacity(assignment.concretes.len());

    for (guard, rhs) in &assignment.concretes {
        let not_prior = protocol.not_guard(ctx, prior);
        let effective_guard = protocol.and_guard(ctx, not_prior, *guard);
        if effective_guard != ctx.get_false() {
            effective.push((effective_guard, *rhs));
        }
        prior = protocol.or_guard(ctx, prior, *guard);
    }

    effective
}

fn coalesce_concretes(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    concretes: Vec<(ExprRef, ExprRef)>,
) -> Vec<(ExprRef, ExprRef)> {
    let mut coalesced = Vec::with_capacity(concretes.len());
    for (guard, rhs) in concretes {
        if let Some((existing_guard, existing_rhs)) = coalesced.last_mut()
            && *existing_rhs == rhs
        {
            *existing_guard = protocol.or_guard(ctx, *existing_guard, guard);
        } else {
            coalesced.push((guard, rhs));
        }
    }
    coalesced
}

fn concretes_without_dont_care(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> Vec<(ExprRef, ExprRef)> {
    let not_dont_care = protocol.not_guard(ctx, assignment.dont_care);
    assignment
        .concretes
        .iter()
        .filter_map(|(guard, rhs)| {
            let guard = protocol.and_guard(ctx, not_dont_care, *guard);
            (guard != ctx.get_false()).then_some((guard, *rhs))
        })
        .collect()
}

pub fn merge_ordered_assignment(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    // Ordered contraction preserves source order: the later action wins over
    // the earlier action. Therefore the new summary's preferences come first.
    let new_concretes = concrete_coverage(ctx, protocol, &new);
    let not_new_concretes = protocol.not_guard(ctx, new_concretes);
    let old_dont_care = protocol.and_guard(ctx, not_new_concretes, existing.dont_care);
    let dont_care = protocol.or_guard(ctx, new.dont_care, old_dont_care);

    let mut concretes = new.concretes;
    concretes.extend(existing.concretes);

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn merge_unordered_assignment(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    // Check conflicts using effective guards, but do not put those expanded
    // guards in the merged assignment. The raw vectors already carry their
    // precedence through their order.
    let mut prior_existing = existing.dont_care;
    for (existing_guard, existing_rhs) in &existing.concretes {
        let not_prior_existing = protocol.not_guard(ctx, prior_existing);
        let existing_effective = protocol.and_guard(ctx, not_prior_existing, *existing_guard);
        let mut prior_new = new.dont_care;

        for (new_guard, new_rhs) in &new.concretes {
            let not_prior_new = protocol.not_guard(ctx, prior_new);
            let new_effective = protocol.and_guard(ctx, not_prior_new, *new_guard);

            if existing_rhs != new_rhs {
                let overlap = protocol.and_guard(ctx, existing_effective, new_effective);
                if overlap != ctx.get_false() {
                    record_internal_assert(ctx, protocol, internal_assert_guard, overlap);
                }
            }

            prior_new = protocol.or_guard(ctx, prior_new, *new_guard);
        }

        prior_existing = protocol.or_guard(ctx, prior_existing, *existing_guard);
    }

    let mut existing_concretes = concrete_coverage(ctx, protocol, &existing);
    existing_concretes = protocol.simplifier.simplify(ctx, existing_concretes);
    let mut new_concretes = concrete_coverage(ctx, protocol, &new);
    new_concretes = protocol.simplifier.simplify(ctx, new_concretes);

    let not_new_concretes = protocol.not_guard(ctx, new_concretes);
    let existing_dont_care = protocol.and_guard(ctx, not_new_concretes, existing.dont_care);
    let not_existing_concretes = protocol.not_guard(ctx, existing_concretes);
    let new_dont_care = protocol.and_guard(ctx, not_existing_concretes, new.dont_care);
    let dont_care = protocol.or_guard(ctx, existing_dont_care, new_dont_care);

    let mut concretes = concretes_without_dont_care(ctx, protocol, &existing);
    concretes.extend(concretes_without_dont_care(ctx, protocol, &new));
    let concretes = coalesce_concretes(ctx, protocol, concretes);

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn merge_disjoint_assignments(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignments: Vec<Assignment>,
) -> Assignment {
    let mut dont_care = ctx.get_false();
    let mut concretes = Vec::new();

    for assignment in assignments {
        dont_care = protocol.or_guard(ctx, dont_care, assignment.dont_care);
        let group = coalesce_concretes(ctx, protocol, assignment.concretes);
        let prior_groups_end = concretes.len();

        for (guard, rhs) in group {
            let existing = concretes[..prior_groups_end]
                .iter()
                .position(|(_, existing_rhs)| *existing_rhs == rhs);
            if let Some(index) = existing {
                concretes[index].0 = protocol.or_guard(ctx, concretes[index].0, guard);
            } else {
                concretes.push((guard, rhs));
            }
        }
    }

    Assignment {
        dont_care,
        concretes,
    }
}

pub fn merge_disjoint_guarded_assignments(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    groups: Vec<(ExprRef, Assignment)>,
) -> (Assignment, ExprRef) {
    let mut dont_care = ctx.get_false();
    let mut coverage = ctx.get_false();
    let mut concretes = Vec::new();

    for (guard, assignment) in groups {
        let local_coverage = concrete_coverage(ctx, protocol, &assignment);
        let guarded_coverage = protocol.and_guard(ctx, guard, local_coverage);
        coverage = protocol.or_guard(ctx, coverage, guarded_coverage);
        let guarded_dont_care = protocol.and_guard(ctx, guard, assignment.dont_care);
        dont_care = protocol.or_guard(ctx, dont_care, guarded_dont_care);

        let unclipped = concretes_without_dont_care(ctx, protocol, &assignment);
        let guarded = unclipped
            .into_iter()
            .map(|(branch, rhs)| (protocol.and_guard(ctx, guard, branch), rhs))
            .collect();
        let group = coalesce_concretes(ctx, protocol, guarded);
        let prior_groups_end = concretes.len();

        for (branch, rhs) in group {
            let existing = concretes[..prior_groups_end]
                .iter()
                .position(|(_, existing_rhs)| *existing_rhs == rhs);
            if let Some(index) = existing {
                concretes[index].0 = protocol.or_guard(ctx, concretes[index].0, branch);
            } else {
                concretes.push((branch, rhs));
            }
        }
    }

    (
        Assignment {
            dont_care,
            concretes,
        },
        coverage,
    )
}

pub fn merge_unordered_assignment_with_disjoint_batch(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    internal_assert_guard: &mut Option<ExprRef>,
    existing: Assignment,
    groups: Vec<(ExprRef, Assignment)>,
) -> Assignment {
    let existing_effective = effective_concretes(ctx, protocol, &existing);
    for (group_guard, group) in &groups {
        for (existing_guard, existing_rhs) in &existing_effective {
            for (branch_guard, group_rhs) in effective_concretes(ctx, protocol, group) {
                if existing_rhs == &group_rhs {
                    continue;
                }
                let guarded_branch = protocol.and_guard(ctx, *group_guard, branch_guard);
                let overlap = protocol.and_guard(ctx, *existing_guard, guarded_branch);
                if overlap != ctx.get_false() {
                    record_internal_assert(ctx, protocol, internal_assert_guard, overlap);
                }
            }
        }
    }

    let (batch, batch_coverage) = merge_disjoint_guarded_assignments(ctx, protocol, groups);
    if existing.dont_care == ctx.get_true() && existing.concretes.is_empty() {
        let dont_care = protocol.not_guard(ctx, batch_coverage);
        return Assignment {
            dont_care,
            concretes: batch.concretes,
        };
    }

    let existing_coverage = concrete_coverage(ctx, protocol, &existing);
    let not_batch_coverage = protocol.not_guard(ctx, batch_coverage);
    let existing_dont_care = protocol.and_guard(ctx, not_batch_coverage, existing.dont_care);
    let not_existing_coverage = protocol.not_guard(ctx, existing_coverage);
    let batch_dont_care = protocol.and_guard(ctx, not_existing_coverage, batch.dont_care);

    let mut concretes = concretes_without_dont_care(ctx, protocol, &existing);
    concretes.extend(batch.concretes);

    Assignment {
        dont_care: protocol.or_guard(ctx, existing_dont_care, batch_dont_care),
        concretes: coalesce_concretes(ctx, protocol, concretes),
    }
}

fn merge_disjoint_assignment(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    merge_disjoint_assignments(ctx, protocol, vec![existing, new])
}

pub fn append_action(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    internal_assert_guard: &mut Option<ExprRef>,
    action: Action,
    ordered: bool,
) {
    append_action_with_mode(
        ctx,
        protocol,
        symbols,
        actions,
        internal_assert_guard,
        action,
        if ordered {
            ActionMergeMode::Ordered
        } else {
            ActionMergeMode::Unordered
        },
    );
}

pub fn append_action_disjoint(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    action: Action,
) {
    append_action_with_mode(
        ctx,
        protocol,
        symbols,
        actions,
        &mut None,
        action,
        ActionMergeMode::Disjoint,
    );
}

enum ActionMergeMode {
    Ordered,
    Unordered,
    Disjoint,
}

fn append_action_with_mode(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &mut Vec<Action>,
    internal_assert_guard: &mut Option<ExprRef>,
    action: Action,
    mode: ActionMergeMode,
) {
    match protocol[action.op].clone() {
        Op::Assign(symbol_id, assignment) => {
            assert_eq!(
                action.guard,
                ctx.get_true(),
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
                ctx.get_true(),
                "assignment action guards must be 1; path conditions belong in Assignment"
            );
            let existing_assignment = match protocol[actions[idx].op].clone() {
                Op::Assign(_, existing_assignment) => existing_assignment,
                _ => unreachable!(),
            };

            let merged_assignment = match mode {
                ActionMergeMode::Ordered => {
                    merge_ordered_assignment(ctx, protocol, existing_assignment, assignment)
                }
                ActionMergeMode::Unordered => merge_unordered_assignment(
                    ctx,
                    protocol,
                    internal_assert_guard,
                    existing_assignment,
                    assignment,
                ),
                ActionMergeMode::Disjoint => {
                    merge_disjoint_assignment(ctx, protocol, existing_assignment, assignment)
                }
            };

            let new_op = protocol.o(Op::Assign(symbol_id, merged_assignment));
            actions[idx].guard = ctx.get_true();
            actions[idx].op = new_op;
        }
        Op::Fork => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Fork))
            {
                if !matches!(mode, ActionMergeMode::Disjoint) {
                    let overlap = protocol.and_guard(ctx, existing_action.guard, action.guard);
                    record_internal_assert(ctx, protocol, internal_assert_guard, overlap);
                }
                existing_action.guard = protocol.or_guard(ctx, existing_action.guard, action.guard);
            } else {
                actions.push(action);
            }
        }
        Op::Done => {
            if let Some(existing_action) = actions
                .iter_mut()
                .find(|prior_action| matches!(protocol[prior_action.op], Op::Done))
            {
                existing_action.guard = protocol.or_guard(ctx, existing_action.guard, action.guard);
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

// Compose this node's register updates with the preceding non-step path.
// All update RHSs read the incoming map. Other actions and edges see the updates.
// Expressions already emitted for preceding nodes are never rewritten again.
fn resolve_registers(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    mut node: Node,
    values: &mut FxHashMap<ExprRef, ExprRef>,
) -> Node {
    let mut updates = FxHashMap::default();
    for action in &mut node.actions {
        if let Op::Assign(register, _) = graph[action.op]
            && symbols[register].kind() == SymbolKind::AutomatonState
        {
            let op = graph[action.op].remap(ctx, values, &FxHashMap::default());
            let Op::Assign(_, assignment) = &op else {
                unreachable!()
            };
            assert_eq!(action.guard, ctx.get_true());
            assert_eq!(
                assignment.dont_care,
                ctx.get_false(),
                "generated registers must not assign X"
            );
            let current = graph.symbol_expr(register).unwrap();
            let held = values.get(&current).copied().unwrap_or(current);
            let value = assignment
                .concretes
                .iter()
                .rev()
                .fold(held, |value, &(guard, rhs)| ctx.ite(guard, rhs, value));
            let value = graph.simplifier.simplify(ctx, value);
            assert!(
                updates.insert(current, value).is_none(),
                "multiple register updates in one node"
            );
            action.op = graph.o(op);
        }
    }
    values.extend(updates);
    for action in &mut node.actions {
        if !matches!(graph[action.op], Op::Assign(r, _) if symbols[r].kind() == SymbolKind::AutomatonState)
        {
            let op = graph[action.op].remap(ctx, values, &FxHashMap::default());
            action.op = graph.o(op);
            action.guard = remap_expr(ctx, action.guard, values);
        }
    }
    for edge in &mut node.transitions {
        edge.guard = remap_expr(ctx, edge.guard, values);
    }
    node
}

pub fn contract_edges(ctx: &mut Context, pg: &mut ProtoGraph, symbols: &SymbolTable) {
    contract_edges_from(ctx, pg, symbols, pg.entry);
}

/// returns `protocol` with semantic behavior preserved, but no non-step edges
pub fn contract_edges_from(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    start: NodeId,
) {
    let node_ids = reachable_node_ids(ctx, protocol, start);
    // A previously contracted target already contains composed expressions.
    // Start each register path from original nodes so updates are applied once.
    let originals = node_ids.iter()
        .any(|node| protocol[*node].actions.iter().any(|a| matches!(protocol[a.op], Op::Assign(r, _) if symbols[r].kind() == SymbolKind::AutomatonState)))
        .then(|| {
            protocol
                .nodes()
                .map(|(id, node)| (id, node.clone()))
                .collect::<FxHashMap<_, _>>()
        });

    for source_node_id in node_ids.into_iter().rev() {
        let mut values = FxHashMap::default();
        let source = match &originals {
            Some(nodes) => resolve_registers(
                ctx,
                protocol,
                symbols,
                nodes[&source_node_id].clone(),
                &mut values,
            ),
            None => protocol[source_node_id].clone(),
        };
        let mut contracted_actions = Vec::with_capacity(source.actions.len());
        let mut internal_assert_guard = None;
        for action in source.actions {
            append_action(
                ctx,
                protocol,
                symbols,
                &mut contracted_actions,
                &mut internal_assert_guard,
                action,
                true,
            );
        }

        let (mut step_transitions, pending_transitions): (Vec<_>, Vec<_>) = source
            .transitions
            .into_iter()
            .partition(|transition| transition.consumes_step);

        let mut pending_transitions: VecDeque<_> = pending_transitions
            .into_iter()
            .rev()
            .map(|transition| {
                (
                    transition,
                    {
                        let mut path = BTreeSet::new();
                        path.insert(source_node_id);
                        path
                    },
                    values.clone(),
                )
            })
            .collect();

        while let Some((transition, path, mut values)) = pending_transitions.pop_front() {
            assert!(!transition.consumes_step);

            let target_node_id = transition.target;
            if path.contains(&target_node_id) {
                internal_assert_guard = Some(match internal_assert_guard.take() {
                    Some(existing_guard) => {
                        protocol.or_guard(ctx, existing_guard, transition.guard)
                    }
                    None => transition.guard,
                });
                continue;
            }

            let incoming_guard = transition.guard;
            let target = match &originals {
                Some(nodes) => resolve_registers(
                    ctx,
                    protocol,
                    symbols,
                    nodes[&target_node_id].clone(),
                    &mut values,
                ),
                None => protocol[target_node_id].clone(),
            };
            let target_actions = target.actions;
            let target_transitions = target.transitions;
            let mut next_path = path.clone();
            next_path.insert(target_node_id);

            for action in target_actions {
                let merged_action = match protocol[action.op].clone() {
                    Op::Assign(symbol_id, assignment) => {
                        assert_eq!(
                            action.guard,
                            ctx.get_true(),
                            "assignment action guards must be 1; path conditions belong in Assignment"
                        );
                        let guarded_assignment =
                            guard_assignment(ctx, protocol, assignment, incoming_guard);
                        let guarded_op = protocol.o(Op::Assign(symbol_id, guarded_assignment));
                        Action::new(ctx.get_true(), guarded_op)
                    }
                    _ => Action::with_guard(
                        &action,
                        protocol.and_guard(ctx, incoming_guard, action.guard),
                    ),
                };
                append_action(
                    ctx,
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
                    protocol.and_guard(ctx, incoming_guard, target_transition.guard),
                );
                if contracted_transition.consumes_step {
                    step_transitions.push(contracted_transition);
                } else {
                    pending_transitions.push_back((
                        contracted_transition,
                        next_path.clone(),
                        values.clone(),
                    ));
                }
            }
        }

        // Merge the path-guarded writes into one simultaneous final update.
        // Checks above already contain the expressions at their observation.
        if originals.is_some() {
            for action in &mut contracted_actions {
                if let Op::Assign(register, assignment) = &protocol[action.op]
                    && symbols[*register].kind() == SymbolKind::AutomatonState
                {
                    let register = *register;
                    let held = protocol.symbol_expr(register).unwrap();
                    let value = assignment
                        .concretes
                        .iter()
                        .rev()
                        .fold(held, |value, &(g, rhs)| ctx.ite(g, rhs, value));
                    let value = protocol.simplifier.simplify(ctx, value);
                    action.op = protocol.o(Op::Assign(
                        register,
                        Assignment::concrete(ctx.get_false(), ctx.get_true(), value),
                    ));
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
pub fn normalize_assignments(ctx: &mut Context, protocol: &mut ProtoGraph, symbols: &SymbolTable) {
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
            let symbol_expr = symbol_expr(ctx, protocol, symbols, symbol_id);
            let assignment = Assignment::concrete(ctx.get_false(), ctx.get_true(), symbol_expr);
            let op = protocol.o(Op::Assign(symbol_id, assignment));
            protocol.push_action(node_id, Action::new(ctx.get_true(), op))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::ROOT_SCOPE;
    use baa::{BitVecOps, BitVecValue};
    use cranelift_entity::EntityRef;
    use patronus::expr::{SerializableIrNode, SymbolValueStore, eval_expr};

    fn register_graph() -> (Context, ProtoGraph, SymbolTable, SymbolId, ExprRef) {
        let mut ctx = Context::default();
        let mut symbols = SymbolTable::default();
        let r = symbols.add_without_parent(
            "r".into(),
            FrontType::BitVec(8),
            SymbolKind::AutomatonState,
        );
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let expr = ctx.bv_symbol("r", 8);
        graph.cache_symbol_expr(r, expr);
        (ctx, graph, symbols, r, expr)
    }

    fn bv(ctx: &Context, store: &SymbolValueStore, expr: ExprRef) -> BitVecValue {
        eval_expr(ctx, store, expr).try_into().unwrap()
    }

    #[test]
    fn register_checks_are_frozen_and_edges_see_updates_once() {
        let (mut ctx, mut graph, symbols, r, current) = register_graph();
        let entry = graph.entry;
        let middle = graph.n(Node::empty());
        let after_step = graph.n(Node::empty());
        let otherwise = graph.n(Node::empty());
        let g = ctx.bv_symbol("g", 1);
        let one = ctx.one(8);
        let first = ctx.add(current, one);
        let two = ctx.bit_vec_val(2, 8);
        let second = ctx.add(current, two);
        let op = graph.o(Op::Assign(
            r,
            Assignment {
                dont_care: ctx.get_false(),
                concretes: vec![
                    (g, first),
                    (ctx.get_true(), second),
                    (ctx.get_true(), current),
                ],
            },
        ));
        graph.push_action(entry, Action::new(ctx.get_true(), op));
        let three = ctx.bit_vec_val(3, 8);
        let check = graph.o(Op::AssertEq(current, three));
        let guard = ctx.equal(current, three);
        graph.push_action(entry, Action::new(guard, check));
        graph.push_transition(entry, Transition::new(ctx.get_true(), middle, false));
        let four = ctx.bit_vec_val(4, 8);
        let next = ctx.add(current, four);
        let op = graph.o(Op::Assign(
            r,
            Assignment::concrete(ctx.get_false(), ctx.get_true(), next),
        ));
        graph.push_action(middle, Action::new(ctx.get_true(), op));
        let seven = ctx.bit_vec_val(7, 8);
        let check = graph.o(Op::AssertEq(current, seven));
        graph.push_action(middle, Action::new(ctx.get_true(), check));
        let guard = ctx.equal(current, seven);
        let not_guard = ctx.not(guard);
        graph.push_transition(middle, Transition::new(guard, after_step, true));
        graph.push_transition(middle, Transition::new(not_guard, otherwise, true));
        let eight = ctx.bit_vec_val(8, 8);
        let next = ctx.add(current, eight);
        let op = graph.o(Op::Assign(
            r,
            Assignment::concrete(ctx.get_false(), ctx.get_true(), next),
        ));
        graph.push_action(after_step, Action::new(ctx.get_true(), op));
        graph.push_transition(
            after_step,
            Transition::new(ctx.get_true(), after_step, true),
        );

        contract_edges(&mut ctx, &mut graph, &symbols);
        let checks = graph[entry]
            .actions
            .iter()
            .filter_map(|a| match graph[a.op] {
                Op::AssertEq(lhs, _) => Some((a.guard, lhs)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(checks.len(), 2);
        for initial in 0..8 {
            for select in [false, true] {
                let mut store = SymbolValueStore::default();
                store.define_bv(current, &BitVecValue::from_u64(initial, 8));
                store.define_bv(g, &BitVecValue::from_u64(select as u64, 1));
                let first = initial + if select { 1 } else { 2 };
                assert_eq!(
                    bv(&ctx, &store, checks[0].1),
                    BitVecValue::from_u64(first, 8)
                );
                assert_eq!(!bv(&ctx, &store, checks[0].0).is_zero(), first == 3);
                assert_eq!(
                    bv(&ctx, &store, checks[1].1),
                    BitVecValue::from_u64(first + 4, 8)
                );
                assert_eq!(
                    !bv(
                        &ctx,
                        &store,
                        graph[entry]
                            .transitions
                            .iter()
                            .find(|e| e.target == after_step)
                            .unwrap()
                            .guard
                    )
                    .is_zero(),
                    first + 4 == 7
                );
                let Op::Assign(_, assignment) = &graph[graph[after_step].actions[0].op] else {
                    unreachable!()
                };
                assert_eq!(
                    bv(&ctx, &store, assignment.concretes[0].1),
                    BitVecValue::from_u64(initial + 8, 8)
                );
            }
        }
    }

    #[test]
    fn register_updates_on_alternative_paths_stay_separate() {
        let (mut ctx, mut graph, symbols, r, current) = register_graph();
        let entry = graph.entry;
        let left = graph.n(Node::empty());
        let right = graph.n(Node::empty());
        let join = graph.n(Node::empty());
        let end = graph.n(Node::empty());
        let g = ctx.bv_symbol("g", 1);
        let not_g = ctx.not(g);
        graph.push_transition(entry, Transition::new(g, left, false));
        graph.push_transition(entry, Transition::new(not_g, right, false));
        for (node, increment) in [(left, 1), (right, 2)] {
            let increment = ctx.bit_vec_val(increment, 8);
            let value = ctx.add(current, increment);
            let op = graph.o(Op::Assign(
                r,
                Assignment::concrete(ctx.get_false(), ctx.get_true(), value),
            ));
            graph.push_action(node, Action::new(ctx.get_true(), op));
            graph.push_transition(node, Transition::new(ctx.get_true(), join, false));
        }
        let nine = ctx.bit_vec_val(9, 8);
        let check = graph.o(Op::AssertEq(current, nine));
        graph.push_action(join, Action::new(ctx.get_true(), check));
        graph.push_transition(join, Transition::new(ctx.get_true(), end, true));
        contract_edges(&mut ctx, &mut graph, &symbols);
        for select in [false, true] {
            let mut store = SymbolValueStore::default();
            store.define_bv(current, &BitVecValue::from_u64(7, 8));
            store.define_bv(g, &BitVecValue::from_u64(select as u64, 1));
            let expected = BitVecValue::from_u64(if select { 8 } else { 9 }, 8);
            let mut checked = 0;
            for action in &graph[entry].actions {
                if bv(&ctx, &store, action.guard).is_zero() {
                    continue;
                }
                match &graph[action.op] {
                    Op::AssertEq(lhs, _) => {
                        assert_eq!(bv(&ctx, &store, *lhs), expected);
                        checked += 1;
                    }
                    Op::Assign(_, assignment) => {
                        let (_, rhs) = assignment
                            .concretes
                            .iter()
                            .find(|(g, _)| !bv(&ctx, &store, *g).is_zero())
                            .unwrap();
                        assert_eq!(bv(&ctx, &store, *rhs), expected);
                    }
                    _ => {}
                }
            }
            assert_eq!(checked, 1);
        }
    }

    fn concrete_assignment(ctx: &Context, rhs: ExprRef) -> Assignment {
        Assignment::concrete(ctx.get_false(), ctx.get_true(), rhs)
    }

    fn dont_care_assignment(ctx: &Context) -> Assignment {
        Assignment::dont_care(ctx.get_true())
    }

    fn expr_str(ctx: &Context, expr: ExprRef) -> String {
        expr.serialize_to_str(ctx)
    }

    #[test]
    fn allows_overlapping_dont_care_and_concrete_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let symbol_id = SymbolId::new(0);
        let symbol = ctx.bv_symbol("signal", 1);
        let dont_care = ctx.bv_symbol("dont_care", 1);
        let concrete = ctx.bv_symbol("concrete", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let concrete_op = protocol.o(Op::Assign(symbol_id, concrete_assignment(&ctx, concrete)));
        let dont_care_op = protocol.o(Op::Assign(symbol_id, dont_care_assignment(&ctx)));
        let mut actions = vec![Action::new(ctx.get_true(), concrete_op)];
        let mut internal_assert_guard = None;
        let true_id = ctx.get_true();
        append_action(
            &mut ctx,
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
        assert_eq!(expr_str(&ctx, assignment.dont_care), "1'b1");
        assert_eq!(assignment.concretes, vec![(ctx.get_true(), concrete)]);
    }

    #[test]
    fn synthesizes_internal_assert_for_overlapping_unordered_assignments() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let symbol_id = SymbolId::new(0);
        let symbol = ctx.bv_symbol("signal", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);

        // Node A: [p] DUT.a := 1
        // Node B: [q] DUT.a := 2
        // Node C: [r] DUT.a := 3
        let p = ctx.bv_symbol("p", 1);
        let q = ctx.bv_symbol("q", 1);
        let r = ctx.bv_symbol("r", 1);
        let one = ctx.bv_symbol("one", 1);
        let two = ctx.bv_symbol("two", 1);
        let three = ctx.bv_symbol("three", 1);

        let mut actions = Vec::new();
        let mut internal_assert_guard = None;
        for (guard, rhs) in [(p, one), (q, two), (r, three)] {
            let assignment = Assignment::concrete(ctx.get_false(), guard, rhs);
            let op = protocol.o(Op::Assign(symbol_id, assignment));
            let true_id = ctx.get_true();
            append_action(
                &mut ctx,
                &mut protocol,
                &SymbolTable::default(),
                &mut actions,
                &mut internal_assert_guard,
                Action::new(true_id, op),
                false,
            );
        }

        assert_eq!(actions.len(), 1);
        assert_ne!(actions[0].guard, ctx.get_false());

        // assert any two guards being run together. (p and q) or (p and r)
        assert_eq!(
            expr_str(&ctx, internal_assert_guard.unwrap()),
            "or(or(and(p, q), and(p, r)), and(and(not(p), q), r))"
        );
    }

    #[test]
    fn unordered_assignment_merge_preserves_ordered_ite_precedence() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let symbol_id = SymbolId::new(0);
        let symbol = ctx.bv_symbol("DUT.a", 1);
        let dont_care = ctx.bv_symbol("dont_care", 1);
        let three = ctx.bv_symbol("three", 1);
        let four = ctx.bv_symbol("four", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let q = ctx.bv_symbol("q", 1);
        let r = ctx.bv_symbol("r", 1);
        let s = ctx.bv_symbol("s", 1);

        // Node A: [1] DUT.a := { X if s; 3 if q }
        // Node B: [1] DUT.a := { 4 if r }

        let true_id = ctx.get_true();
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
                dont_care: ctx.get_false(),
                concretes: vec![(r, four)],
            },
        ));

        let mut actions = vec![Action::new(true_id, node_a_op)];
        let mut internal_assert_guard = None;

        append_action(
            &mut ctx,
            &mut protocol,
            &SymbolTable::default(),
            &mut actions,
            &mut internal_assert_guard,
            Action::new(true_id, node_b_op),
            false,
        );

        assert_eq!(actions.len(), 1);
        assert_ne!(actions[0].guard, ctx.get_false());

        // q and r are our concrete assignments to 3 and 4. assignment to 3 only triggers if
        // not s , so there is only a conflicting assignment under ((not s) and q and r)
        assert_eq!(
            expr_str(&ctx, internal_assert_guard.unwrap()),
            "and(and(not(s), q), r)"
        );

        protocol.simplify_all_exprs(&mut ctx);

        let Op::Assign(_, assignment) = protocol[actions[0].op].clone() else {
            panic!("expected assignment");
        };

        // Concrete branches from both unordered sides are preferred over DontCare, but the
        // original node-local DontCare still suppresses node A's own concrete branch.
        assert_eq!(expr_str(&ctx, assignment.dont_care), "and(not(r), s)");
        let not_s = protocol.not_guard(&mut ctx, s);
        let effective_q = protocol.and_guard(&mut ctx, not_s, q);
        assert_eq!(assignment.concretes, vec![(effective_q, three), (r, four)]);
    }

    #[test]
    fn unordered_assignment_merge_allows_overlapping_equal_concretes() {
        let mut protocol = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let symbol_id = SymbolId::new(0);
        let symbol = ctx.bv_symbol("DUT.a", 1);
        let dont_care = ctx.bv_symbol("dont_care", 1);
        let three = ctx.bv_symbol("three", 1);
        protocol.cache_symbol_expr(symbol_id, symbol);
        protocol.dont_cares.insert(dont_care);

        let p = ctx.bv_symbol("p", 1);
        let q = ctx.bv_symbol("q", 1);
        let r = ctx.bv_symbol("r", 1);

        let true_id = ctx.get_true();
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
                dont_care: ctx.get_false(),
                concretes: vec![(r, three)],
            },
        ));

        let mut actions = vec![Action::new(true_id, node_a_op)];
        let mut internal_assert_guard = None;

        append_action(
            &mut ctx,
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
        let mut ctx = Context::default();
        let p = ctx.bv_symbol("p", 1);
        let q = ctx.bv_symbol("q", 1);
        let r = ctx.bv_symbol("r", 1);

        let fork1 = protocol.o(Op::Fork);
        let fork2 = protocol.o(Op::Fork);
        let fork3 = protocol.o(Op::Fork);
        protocol.node_mut(protocol.entry).actions = vec![
            Action::new(p, fork1),
            Action::new(q, fork2),
            Action::new(r, fork3),
        ];

        contract_edges(&mut ctx, &mut protocol, &SymbolTable::default());

        let actions = &protocol[protocol.entry].actions;
        assert_eq!(actions.len(), 2);
        assert!(matches!(protocol[actions[0].op], Op::Fork));
        assert!(matches!(protocol[actions[1].op], Op::InternalAssertFalse));

        let fork_guard = ctx[actions[0].guard].serialize_to_str(&ctx);
        let internal_guard = ctx[actions[1].guard].serialize_to_str(&ctx);

        // any of the forks can trigger: (p or q or r)
        assert_eq!(fork_guard, "or(or(p, q), r)");

        // any two of the forks should not trigger at once
        // below expression is equivalent to (p or q) and (p or r) and (q or r)
        assert_eq!(internal_guard, "or(and(p, q), and(or(p, q), r))");
    }
}
