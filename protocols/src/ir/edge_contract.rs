use std::collections::BTreeSet;

use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, remap_expr,
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

/// Concrete Coverage (not accounting for DontCare)
pub fn raw_concrete_coverage(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> ExprRef {
    assignment
        .concretes
        .iter()
        .fold(ctx.get_false(), |coverage, &(guard, _)| {
            protocol.or_guard(ctx, coverage, guard)
        })
}

pub fn concrete_coverage(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> ExprRef {
    let raw_coverage = raw_concrete_coverage(ctx, protocol, assignment);
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
    let existing_effective = effective_concretes(ctx, protocol, &existing);
    let new_effective = effective_concretes(ctx, protocol, &new);
    for &(existing_guard, existing_rhs) in &existing_effective {
        for &(new_guard, new_rhs) in &new_effective {
            if existing_rhs != new_rhs {
                let overlap = protocol.and_guard(ctx, existing_guard, new_guard);
                if overlap != ctx.get_false() {
                    record_internal_assert(ctx, protocol, internal_assert_guard, overlap);
                }
            }
        }
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
        concretes.extend(assignment.concretes);
    }

    Assignment {
        dont_care,
        concretes: coalesce_concretes(ctx, protocol, concretes),
    }
}

pub fn merge_disjoint_guarded_assignments(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    groups: Vec<(ExprRef, Assignment)>,
) -> Assignment {
    let assignments = groups
        .into_iter()
        .map(|(guard, assignment)| guard_disjoint_assignment(ctx, protocol, assignment, guard))
        .collect();
    merge_disjoint_assignments(ctx, protocol, assignments)
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

/// Since assignments don't take effect until the step edge,
/// Rewrite assertions, guards, transitions to use newly assigned values
fn normalize_node(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    node: Node,
) -> Node {
    let mut actions = Vec::new();
    let mut error = None;
    for action in node.actions {
        append_action(ctx, graph, symbols, &mut actions, &mut error, action, true);
    }
    if let Some(guard) = error {
        let op = graph.o(Op::InternalAssertFalse);
        actions.push(Action::new(guard, op));
    }
    let values = assigned_values(ctx, graph, symbols, &actions);
    for action in &mut actions {
        if !matches!(graph[action.op], Op::Assign(..)) {
            let op = graph[action.op].remap(ctx, &values, &FxHashMap::default());
            action.op = graph.o(op);
            action.guard = remap_expr(ctx, action.guard, &values);
        }
    }
    let transitions = node
        .transitions
        .into_iter()
        .map(|mut edge| {
            edge.guard = remap_expr(ctx, edge.guard, &values);
            edge
        })
        .collect();
    Node {
        actions,
        transitions,
    }
}

// For every symbol assigned to, return its `ExprRef` verison and what it's assigned to
// in `actions`.
fn assigned_values(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &[Action],
) -> FxHashMap<ExprRef, ExprRef> {
    let mut values = FxHashMap::default();
    for action in actions {
        if let Op::Assign(target, assignment) = graph[action.op].clone() {
            let held = symbol_expr(ctx, graph, symbols, target);
            let x = if symbols[target].is_in_port() && assignment.dont_care != ctx.get_false() {
                graph.dont_care_input(ctx, symbols, target)
            } else {
                assert_eq!(assignment.dont_care, ctx.get_false(), "state cannot be X");
                held
            };
            let value = assignment.to_expr(ctx, x, held);
            let value = ctx.ite(action.guard, value, held);
            let value = graph.simplifier.simplify(ctx, value);
            values.insert(held, value);
        }
    }
    values
}

pub fn contract_edges(ctx: &mut Context, pg: &mut ProtoGraph, symbols: &SymbolTable) {
    contract_edges_from(ctx, pg, symbols, pg.entry);
}

/// Resolve action order in a raw graph and remove its non-step edges.
/// NOTE: This function is not idempotent!
/// This is due to the use of `normalize_node`, which is not idempotent
pub fn contract_edges_from(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    start: NodeId,
) {
    let node_ids = protocol.reachable_node_ids(ctx, start);
    let mut sources = FxHashMap::default();
    for &id in &node_ids {
        let node = normalize_node(ctx, protocol, symbols, protocol[id].clone());
        sources.insert(id, node);
    }
    for source in node_ids {
        let contracted = contract_node(
            ctx,
            protocol,
            symbols,
            source,
            &sources,
            &mut BTreeSet::new(),
        );
        *protocol.node_mut(source) = contracted;
    }
}

fn same_transition_effect(a: &Transition, b: &Transition) -> bool {
    a.target == b.target && a.consumes_step == b.consumes_step && a.rotations == b.rotations
}

/// Group equal effects and OR their path-guarded conditions.
fn merge_branches(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    branches: Vec<(ExprRef, Node)>,
) -> Node {
    let mut merged = Node::empty();
    for (condition, branch) in branches {
        for mut action in branch.actions {
            if let Op::Assign(target, assignment) = protocol[action.op].clone() {
                let assignment = guard_assignment(ctx, protocol, assignment, condition);
                action.op = protocol.o(Op::Assign(target, assignment));
                append_action_disjoint(ctx, protocol, symbols, &mut merged.actions, action);
            } else {
                action.guard = protocol.and_guard(ctx, condition, action.guard);
                if let Some(prior) = merged
                    .actions
                    .iter_mut()
                    .find(|a| protocol[a.op] == protocol[action.op])
                {
                    prior.guard = protocol.or_guard(ctx, prior.guard, action.guard);
                } else {
                    merged.actions.push(action);
                }
            }
        }
        for mut edge in branch.transitions {
            edge.guard = protocol.and_guard(ctx, condition, edge.guard);
            if let Some(prior) = merged
                .transitions
                .iter_mut()
                .find(|e| same_transition_effect(e, &edge))
            {
                prior.guard = protocol.or_guard(ctx, prior.guard, edge.guard);
            } else {
                merged.transitions.push(edge);
            }
        }
    }
    merged.actions.retain(|a| a.guard != ctx.get_false());
    merged.transitions.retain(|e| e.guard != ctx.get_false());
    merged
}

// Compose mutually exclusive branches, then append their effects in source order.
fn contract_node(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    source: NodeId,
    sources: &FxHashMap<NodeId, Node>,
    path: &mut BTreeSet<NodeId>,
) -> Node {
    path.insert(source);
    let node = sources[&source].clone();
    let values = assigned_values(ctx, protocol, symbols, &node.actions);
    let mut actions = node.actions;
    let mut branches = Vec::new();
    for edge in node.transitions {
        if edge.guard == ctx.get_false() {
            continue;
        }
        let branch = if edge.consumes_step {
            Node {
                actions: vec![],
                transitions: vec![edge.with_guard(ctx.get_true())],
            }
        } else if path.contains(&edge.target) { // Fail on a combintional loop
            let op = protocol.o(Op::InternalAssertFalse);
            Node {
                actions: vec![Action::new(ctx.get_true(), op)],
                transitions: vec![],
            }
        } else {
            // by construction, all branches are mutually exclusive. follow the branch first,
            // and then we'll merge them later
            let mut branch =
                contract_node(ctx, protocol, symbols, edge.target, sources, path);
            for action in &mut branch.actions {
                let op = protocol[action.op].remap(ctx, &values, &FxHashMap::default());
                action.op = protocol.o(op);
                action.guard = remap_expr(ctx, action.guard, &values);
            }
            for transition in &mut branch.transitions {
                transition.guard = remap_expr(ctx, transition.guard, &values);
            }
            branch
        };
        branches.push((edge.guard, branch));
    }

    // merge all the branches together
    let branches = merge_branches(ctx, protocol, symbols, branches);
    let mut error = None;
    for action in branches.actions {
        append_action(
            ctx,
            protocol,
            symbols,
            &mut actions,
            &mut error,
            action,
            true,
        );
    }
    if let Some(guard) = error {
        let op = protocol.o(Op::InternalAssertFalse);
        actions.push(Action::new(guard, op));
    }
    path.remove(&source);
    Node {
        actions,
        transitions: branches.transitions,
    }
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
    use crate::ir::proto_graph::Transition;
    use baa::{BitVecOps, BitVecValue};
    use cranelift_entity::EntityRef;
    use patronus::expr::{SerializableIrNode, SymbolValueStore, eval_expr};

    fn concrete_assignment(ctx: &Context, rhs: ExprRef) -> Assignment {
        Assignment::concrete(ctx.get_false(), ctx.get_true(), rhs)
    }

    fn dont_care_assignment(ctx: &Context) -> Assignment {
        Assignment::dont_care(ctx.get_true())
    }

    fn expr_str(ctx: &Context, expr: ExprRef) -> String {
        expr.serialize_to_str(ctx)
    }

    fn active(ctx: &Context, store: &SymbolValueStore, guard: ExprRef) -> bool {
        let value: BitVecValue = eval_expr(ctx, store, guard).try_into().unwrap();
        !value.is_zero()
    }

    #[test]
    fn state_updates_are_resolved_once_and_stop_at_steps() {
        use crate::backends::transition_system::lower_proto_graph_to_transition_system;
        use patronus::sim::{InitKind, Interpreter, Simulator};
        use patronus::system::TransitionSystem;

        let mut ctx = Context::default();
        let mut symbols = SymbolTable::default();
        let mut graph = ProtoGraph::new(ProtocolContext::new("state_order".into(), ROOT_SCOPE));
        let register = graph.add_register(&mut ctx, &mut symbols, "r", 8);
        let r = graph.symbol_expr(register).unwrap();
        graph.register_inits.insert(register, ctx.zero(8));
        let one = ctx.bit_vec_val(1, 8);
        let two = ctx.bit_vec_val(2, 8);
        let three = ctx.bit_vec_val(3, 8);
        let four = ctx.bit_vec_val(4, 8);
        let increment = ctx.add(r, one);
        let entry = graph.entry;
        let check = graph.n(Node::empty());
        let update = graph.n(Node::empty());
        let check_again = graph.n(Node::empty());
        let second_cycle = graph.n(Node::empty());
        let second_update = graph.n(Node::empty());
        let final_cycle = graph.n(Node::empty());
        for (node, op) in [
            (entry, Op::Assign(register, concrete_assignment(&ctx, two))),
            (check, Op::AssertEq(increment, three)),
            (
                update,
                Op::Assign(register, concrete_assignment(&ctx, increment)),
            ),
            (check_again, Op::AssertEq(r, three)),
            (second_cycle, Op::AssertEq(r, three)),
            (
                second_update,
                Op::Assign(register, concrete_assignment(&ctx, increment)),
            ),
            (final_cycle, Op::AssertEq(r, four)),
            (final_cycle, Op::Done),
        ] {
            let op = graph.o(op);
            graph.push_action(node, Action::new(ctx.get_true(), op));
        }
        for (from, to, step) in [
            (entry, check, false),
            (check, update, false),
            (update, check_again, false),
            (check_again, second_cycle, true),
            (second_cycle, second_update, false),
        ] {
            graph.push_transition(from, Transition::new(ctx.get_true(), to, step));
        }
        // The raw node's edge sees its assignment, whereas its assignment RHS
        // reads the incoming r. The contracted edge must contain r + 1 once.
        let guard = ctx.equal(r, four);
        graph.push_transition(second_update, Transition::new(guard, final_cycle, true));
        contract_edges(&mut ctx, &mut graph, &symbols);
        let expected = ctx.equal(increment, four);
        assert_eq!(graph[second_cycle].transitions[0].guard, expected);

        let core = lower_proto_graph_to_transition_system(
            &mut ctx,
            graph,
            TransitionSystem::new("state_order".into()),
            FxHashMap::default(),
            FxHashMap::default(),
            &symbols,
        );
        let mut sim = Interpreter::new(&ctx, &core.ts);
        sim.init(InitKind::Zero);
        for expected in [3, 4, 4] {
            sim.step();
            assert_eq!(sim.get(r), BitVecValue::from_u64(expected, 8).into());
        }
        assert_eq!(sim.get(core.node_symbol), sim.get(core.done_state));
    }

    #[test]
    fn an_x_release_is_still_observable_after_an_earlier_write() {
        use crate::ir::driver_to_monitor::convert_driver_to_monitor;
        let mut ctx = Context::default();
        let mut diagnostics = crate::frontend::diagnostic::DiagnosticHandler::default();
        let (mut symbols, modules) = crate::frontend(
            &["../tests/synchronous/wire.prot"],
            &mut diagnostics,
            false,
            false,
        )
        .unwrap();
        let context = modules[0].protos[0].ctx.clone();
        let pin = context.dut_input_symbols(&symbols).next().unwrap();
        let mut graph = ProtoGraph::new(context);
        let pin_expr = symbol_expr(&mut ctx, &mut graph, &symbols, pin);
        let entry = graph.entry;
        let release = graph.n(Node::empty());
        let observation = graph.n(Node::empty());
        for (node, op) in [
            (
                entry,
                Op::Assign(pin, concrete_assignment(&ctx, ctx.get_true())),
            ),
            (release, Op::Assign(pin, dont_care_assignment(&ctx))),
            (observation, Op::AssertEq(pin_expr, ctx.get_false())),
            (observation, Op::Done),
        ] {
            let op = graph.o(op);
            graph.push_action(node, Action::new(ctx.get_true(), op));
        }
        graph.push_transition(entry, Transition::new(ctx.get_true(), release, false));
        graph.push_transition(release, Transition::new(ctx.get_true(), observation, false));
        contract_edges(&mut ctx, &mut graph, &symbols);
        let assertion = graph[entry]
            .actions
            .iter()
            .find_map(|a| match graph[a.op] {
                Op::AssertEq(a, _) => Some(a),
                _ => None,
            })
            .unwrap();
        assert!(graph.dont_cares.contains(&assertion));
        let monitor = convert_driver_to_monitor(&mut ctx, graph, &mut symbols).unwrap();
        assert!(monitor.graph[entry].actions.iter().any(|a| {
            matches!(monitor.graph[a.op], Op::AssertEq(lhs, rhs)
                if lhs == pin_expr && rhs == ctx.get_false())
        }));
    }

    #[test]
    fn disjoint_merge_preserves_each_branchs_priority() {
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let branch = ctx.bv_symbol("branch", 1);
        let not_branch = ctx.not(branch);
        let condition = ctx.bv_symbol("condition", 1);
        let one = ctx.bit_vec_val(1, 8);
        let two = ctx.bit_vec_val(2, 8);
        let left = Assignment {
            dont_care: ctx.get_false(),
            concretes: vec![(condition, one), (ctx.get_true(), two)],
        };
        let right = Assignment {
            dont_care: ctx.get_false(),
            concretes: vec![(condition, two), (ctx.get_true(), one)],
        };
        let merged = merge_disjoint_guarded_assignments(
            &mut ctx,
            &mut graph,
            vec![(branch, left), (not_branch, right)],
        );
        for b in [false, true] {
            for c in [false, true] {
                let mut store = SymbolValueStore::default();
                store.define_bv(branch, &BitVecValue::from_u64(b as u64, 1));
                store.define_bv(condition, &BitVecValue::from_u64(c as u64, 1));
                let (_, rhs) = merged
                    .concretes
                    .iter()
                    .find(|(g, _)| active(&ctx, &store, *g))
                    .unwrap();
                assert_eq!(*rhs, if b == c { one } else { two });
            }
        }
    }

    #[test]
    fn contracts_branches_before_sequential_composition() {
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let mut symbols = SymbolTable::default();
        let pin = symbols.add_without_parent(
            "signal".into(),
            FrontType::BitVec(8),
            crate::frontend::symbol::SymbolKind::InPort,
        );
        let b = ctx.bv_symbol("branch", 1);
        let p = ctx.bv_symbol("left_write", 1);
        let q = ctx.bv_symbol("right_write", 1);
        let t = ctx.bv_symbol("later_write", 1);
        let one = ctx.bit_vec_val(1, 8);
        let two = ctx.bit_vec_val(2, 8);
        let three = ctx.bit_vec_val(3, 8);
        let left = graph.n(Node::empty());
        let right = graph.n(Node::empty());
        let join = graph.n(Node::empty());
        let overwrite = graph.n(Node::empty());
        let step = graph.n(Node::empty());
        let end = graph.n(Node::empty());
        let entry = graph.entry;
        for (node, assignment) in [
            (entry, dont_care_assignment(&ctx)),
            (left, Assignment::concrete(ctx.get_false(), p, one)),
            (right, Assignment::concrete(ctx.get_false(), q, two)),
            (overwrite, concrete_assignment(&ctx, three)),
        ] {
            let op = graph.o(Op::Assign(pin, assignment));
            graph.push_action(node, Action::new(ctx.get_true(), op));
        }
        // X; if b { if p { pin := 1 } } else { if q { pin := 2 } };
        // if t { pin := 3 }; step(); done.
        graph.push_transition(entry, Transition::new(b, left, false));
        graph.push_transition(entry, Transition::new(ctx.not(b), right, false));
        for node in [left, right] {
            let fork = graph.o(Op::Fork);
            graph.push_action(node, Action::new(ctx.get_true(), fork));
            graph.push_transition(node, Transition::new(ctx.get_true(), join, false));
        }
        graph.push_transition(join, Transition::new(t, overwrite, false));
        graph.push_transition(join, Transition::new(ctx.not(t), step, false));
        graph.push_transition(overwrite, Transition::new(ctx.get_true(), step, false));
        graph.push_transition(step, Transition::new(ctx.get_true(), end, true));
        let done = graph.o(Op::Done);
        graph.push_action(end, Action::new(ctx.get_true(), done));
        contract_edges(&mut ctx, &mut graph, &symbols);
        let assignment = graph[entry]
            .actions
            .iter()
            .find_map(|a| match &graph[a.op] {
                Op::Assign(_, assignment) => Some(assignment),
                _ => None,
            })
            .unwrap();
        for bits in 0..16 {
            let [bv, pv, qv, tv] = [0, 1, 2, 3].map(|bit| (bits >> bit) & 1 != 0);
            let mut store = SymbolValueStore::default();
            for (expr, value) in [(b, bv), (p, pv), (q, qv), (t, tv)] {
                store.define_bv(expr, &BitVecValue::from_u64(value as u64, 1));
            }
            let expected = if tv {
                Some(three)
            } else if bv && pv {
                Some(one)
            } else if !bv && qv {
                Some(two)
            } else {
                None // the initial X remains in effect
            };
            let actual = if active(&ctx, &store, assignment.dont_care) {
                None
            } else {
                Some(
                    assignment
                        .concretes
                        .iter()
                        .find(|(g, _)| active(&ctx, &store, *g))
                        .unwrap()
                        .1,
                )
            };
            assert_eq!(actual, expected, "branches {bits:04b}");
            let actions: Vec<_> = graph[entry]
                .actions
                .iter()
                .filter(|a| active(&ctx, &store, a.guard))
                .map(|a| &graph[a.op])
                .collect();
            assert_eq!(
                actions.iter().filter(|op| matches!(op, Op::Fork)).count(),
                1
            );
            assert!(
                !actions
                    .iter()
                    .any(|op| matches!(op, Op::Done | Op::InternalAssertFalse))
            );
            let edges: Vec<_> = graph[entry]
                .transitions
                .iter()
                .filter(|e| active(&ctx, &store, e.guard))
                .collect();
            assert_eq!(edges.len(), 1);
            assert!(edges[0].consumes_step);
            assert_eq!(edges[0].target, end);
        }
    }

    #[test]
    fn contraction_preserves_guarded_non_step_cycle_errors() {
        let mut graph = ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE));
        let mut ctx = Context::default();
        let guard = ctx.bv_symbol("cycle", 1);
        let exit = graph.n(Node::empty());
        let entry = graph.entry;
        graph.push_transition(entry, Transition::new(guard, entry, false));
        let not_guard = ctx.not(guard);
        graph.push_transition(entry, Transition::new(not_guard, exit, false));
        let done = graph.o(Op::Done);
        graph.push_action(exit, Action::new(ctx.get_true(), done));
        contract_edges(&mut ctx, &mut graph, &SymbolTable::default());
        assert!(graph[entry].transitions.is_empty());
        assert_eq!(graph[entry].actions.len(), 2);
        for action in &graph[entry].actions {
            match graph[action.op] {
                Op::Done => assert_eq!(action.guard, not_guard),
                Op::InternalAssertFalse => assert_eq!(action.guard, guard),
                _ => panic!("unexpected action"),
            }
        }
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

    #[test]
    fn branch_assignment_merges_preserve_priority_releases_and_missing_writes() {
        for variant in 0..3 {
            let mut ctx = Context::default();
            let mut graph = ProtoGraph::new(ProtocolContext::new("priority".into(), ROOT_SCOPE));
            let mut symbols = SymbolTable::default();
            let pin = symbols.add_without_parent(
                "pin".into(),
                FrontType::BitVec(8),
                crate::frontend::symbol::SymbolKind::InPort,
            );
            let c = ctx.bv_symbol("condition", 1);
            let x = ctx.bv_symbol("release", 1);
            let p = ctx.bv_symbol("first", 1);
            let q = ctx.bv_symbol("other_first", 1);
            let one = ctx.bit_vec_val(1, 8);
            let two = ctx.bit_vec_val(2, 8);
            let old = ctx.bit_vec_val(9, 8);
            let entry = graph.entry;
            let left = graph.n(Node::empty());
            let right = graph.n(Node::empty());
            let join = graph.n(Node::empty());
            let end = graph.n(Node::empty());
            let op = graph.o(Op::Assign(pin, concrete_assignment(&ctx, old)));
            graph.push_action(entry, Action::new(ctx.get_true(), op));
            let op = graph.o(Op::Assign(
                pin,
                Assignment {
                    dont_care: x,
                    concretes: vec![(p, one), (ctx.get_true(), two)],
                },
            ));
            graph.push_action(left, Action::new(ctx.get_true(), op));
            if variant != 2 {
                let (first, fallback) = if variant == 0 { (one, two) } else { (two, one) };
                let op = graph.o(Op::Assign(
                    pin,
                    Assignment {
                        dont_care: ctx.get_false(),
                        concretes: vec![(q, first), (ctx.get_true(), fallback)],
                    },
                ));
                graph.push_action(right, Action::new(ctx.get_true(), op));
            }
            graph.push_transition(entry, Transition::new(c, left, false));
            graph.push_transition(entry, Transition::new(ctx.not(c), right, false));
            for node in [left, right] {
                graph.push_transition(node, Transition::new(ctx.get_true(), join, false));
            }
            graph.push_transition(join, Transition::new(ctx.get_true(), end, true));
            contract_edges(&mut ctx, &mut graph, &symbols);
            let assignment = graph[entry]
                .actions
                .iter()
                .find_map(|a| match &graph[a.op] {
                    Op::Assign(_, assignment) => Some(assignment),
                    _ => None,
                })
                .unwrap();
            assert_eq!(graph[entry].transitions.len(), 1);
            assert_eq!(graph[entry].transitions[0].guard, ctx.get_true());
            for bits in 0..16 {
                let [cv, xv, pv, qv] = [0, 1, 2, 3].map(|i| (bits >> i) & 1 != 0);
                let mut store = SymbolValueStore::default();
                for (symbol, value) in [(c, cv), (x, xv), (p, pv), (q, qv)] {
                    store.define_bv(symbol, &BitVecValue::from_u64(value as u64, 1));
                }
                let expected = if cv {
                    if xv {
                        None
                    } else {
                        Some(if pv { one } else { two })
                    }
                } else if variant == 2 {
                    Some(old)
                } else {
                    Some(if qv == (variant == 0) { one } else { two })
                };
                let actual = if active(&ctx, &store, assignment.dont_care) {
                    None
                } else {
                    assignment
                        .concretes
                        .iter()
                        .find(|(g, _)| active(&ctx, &store, *g))
                        .map(|(_, v)| *v)
                };
                assert_eq!(actual, expected, "variant {variant}, inputs {bits:04b}");
            }
        }
    }

    #[test]
    fn edge_coalescing_preserves_step_and_rotation_effects() {
        use crate::ir::proto_graph::TransitionRotation;
        let mut ctx = Context::default();
        let mut graph = ProtoGraph::new(ProtocolContext::new("effects".into(), ROOT_SCOPE));
        let c = ctx.bv_symbol("condition", 1);
        let end = graph.n(Node::empty());
        let step = Transition::new(ctx.get_true(), end, true);
        let no_step = Transition::new(ctx.get_true(), end, false);
        let mut rotate = step.clone();
        rotate.rotations.push(TransitionRotation {
            protocol: "test".into(),
            amount: 1,
        });
        let branch = |transitions| Node {
            actions: vec![],
            transitions,
        };
        let not_c = ctx.not(c);
        let merged = merge_branches(
            &mut ctx,
            &mut graph,
            &SymbolTable::default(),
            vec![
                (c, branch(vec![step.clone(), no_step.clone()])),
                (not_c, branch(vec![step, rotate.clone()])),
            ],
        );
        assert_eq!(merged.transitions.len(), 3);
        assert_eq!(merged.transitions[0].guard, ctx.get_true());
        assert_eq!(merged.transitions[1], no_step.with_guard(c));
        assert_eq!(merged.transitions[2], rotate.with_guard(not_c));
    }
}
