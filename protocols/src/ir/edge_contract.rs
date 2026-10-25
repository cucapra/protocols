use std::collections::BTreeSet;

use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::proto_graph::{
    Action, Assignment, Node, NodeId, Op, ProtoGraph, Transition, remap_expr,
};
use patronus::expr::{Context, Expr, ExprRef, find_symbols};
use rustc_hash::{FxHashMap, FxHashSet};

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

pub(crate) fn raw_concrete_coverage(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    assignment: &Assignment,
) -> ExprRef {
    let conditions = assignment
        .concretes
        .iter()
        .map(|&(guard, _)| guard)
        .collect::<Vec<_>>();
    let true_guard = ctx.get_true();
    merge_branch_guards(
        ctx,
        protocol,
        &conditions,
        std::iter::repeat_n(true_guard, conditions.len()),
    )
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
            *existing_guard = merge_branch_guards(
                ctx,
                protocol,
                &[*existing_guard, guard],
                [ctx.get_true(); 2].into_iter(),
            );
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
    // Later writes take precedence; uncovered paths retain the earlier write.
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
        // Keep each branch's first-match priority. Joining nonadjacent equal
        // RHSs across branches could move a fallback ahead of an earlier choice.
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
        Op::Data { .. } | Op::Last { .. } | Op::Valid { .. } => {
            // All copies of this load read the same FIFO sample. Unlike an
            // ordinary assignment, Valid also records that this head was visited.
            if let Some(prior) = actions
                .iter_mut()
                .find(|a| protocol[a.op] == protocol[action.op])
            {
                prior.guard = protocol.or_guard(ctx, prior.guard, action.guard);
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

// Normalize one raw node. Assignment RHSs read incoming state; consumers
// observe its completed assignments. Do this once, before composing summaries.
fn normalize_node(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    node: Node,
    reads: &FxHashSet<ExprRef>,
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
    let values = assigned_values(ctx, graph, symbols, &actions, reads);
    for action in &mut actions {
        if graph[action.op].assignment(ctx, graph).is_none() {
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

fn assigned_values(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    actions: &[Action],
    reads: &FxHashSet<ExprRef>,
) -> FxHashMap<ExprRef, ExprRef> {
    let mut values = FxHashMap::default();
    for action in actions {
        if let Some((target, assignment)) = graph[action.op].assignment(ctx, graph) {
            let held = symbol_expr(ctx, graph, symbols, target);
            if symbols[target].is_in_port() && !reads.contains(&held) {
                continue;
            }
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
/// The result is synchronous: all expressions read incoming register state.
/// Do not normalize an already contracted graph again.
pub fn contract_edges_from(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    start: NodeId,
) {
    let node_ids = protocol.reachable_node_ids(ctx, start);
    // Only pins explicitly read by the protocol need an observation expression.
    // In particular, an unused X write does not create a sampled input.
    let mut expressions = Vec::new();
    for &id in &node_ids {
        expressions.extend(protocol[id].transitions.iter().map(|e| e.guard));
        for action in &protocol[id].actions {
            expressions.push(action.guard);
            match &protocol[action.op] {
                Op::Assign(_, a) => {
                    expressions.push(a.dont_care);
                    expressions.extend(a.concretes.iter().flat_map(|&(g, rhs)| [g, rhs]));
                }
                Op::AssertEq(a, b) => expressions.extend([*a, *b]),
                _ => {}
            }
        }
    }
    let reads = expressions
        .into_iter()
        .flat_map(|e| find_symbols(ctx, e))
        .collect();
    let mut sources = FxHashMap::default();
    for &id in &node_ids {
        let node = normalize_node(ctx, protocol, symbols, protocol[id].clone(), &reads);
        sources.insert(id, node);
    }
    for source in node_ids {
        let contracted = contract_node(
            ctx,
            protocol,
            symbols,
            source,
            &sources,
            &reads,
            &mut BTreeSet::new(),
        );
        *protocol.node_mut(source) = contracted;
    }
}

fn merge_branch_guards(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    conditions: &[ExprRef],
    guards: impl Iterator<Item = ExprRef>,
) -> ExprRef {
    let mut choices = conditions.iter().copied().zip(guards).collect::<Vec<_>>();
    // Recover partitions before multiplying in the selected effects. For
    // example, (v & !l, a), (v & l, b), (!v, c) becomes
    // ite(v, ite(!l, a, b), c). Shared effects and coverage then collapse
    // immediately, rather than repeatedly expanding v&!l | v&l downstream.
    loop {
        let pair = (0..choices.len()).find_map(|i| {
            (i + 1..choices.len()).find_map(|j| {
                complementary_branches(ctx, choices[i].0, choices[j].0)
                    .map(|(common, split)| (i, j, common, split))
            })
        });
        let Some((i, j, common, split)) = pair else {
            break;
        };
        let common = common.into_iter().fold(ctx.get_true(), |guard, term| {
            protocol.and_guard(ctx, guard, term)
        });
        let selected = ctx.ite(split, choices[i].1, choices[j].1);
        let selected = protocol.simplifier.simplify(ctx, selected);
        choices[i] = (common, selected);
        choices.remove(j);
    }
    choices
        .into_iter()
        .fold(ctx.get_false(), |prior, (condition, guard)| {
            let guard = protocol.and_guard(ctx, condition, guard);
            protocol.or_guard(ctx, prior, guard)
        })
}

// Return the common guard and binary selector for two complementary branches.
// This is syntactic factoring, not an assumption that the head is exhaustive:
// v&l and v&!l still have coverage v when no empty alternative is present.
fn complementary_branches(
    ctx: &Context,
    lhs: ExprRef,
    rhs: ExprRef,
) -> Option<(Vec<ExprRef>, ExprRef)> {
    fn conjuncts(ctx: &Context, guard: ExprRef, out: &mut Vec<ExprRef>) {
        if let Expr::BVAnd(a, b, _) = ctx[guard] {
            conjuncts(ctx, a, out);
            conjuncts(ctx, b, out);
        } else if !out.contains(&guard) {
            out.push(guard);
        }
    }
    let complements = |a, b| {
        matches!(ctx[a], Expr::BVNot(inner, _) if inner == b)
            || matches!(ctx[b], Expr::BVNot(inner, _) if inner == a)
    };
    if complements(lhs, rhs) {
        return Some((vec![], lhs));
    }
    let (mut left, mut right) = (Vec::new(), Vec::new());
    conjuncts(ctx, lhs, &mut left);
    conjuncts(ctx, rhs, &mut right);
    let common = left
        .iter()
        .copied()
        .filter(|term| right.contains(term))
        .collect::<Vec<_>>();
    left.retain(|term| !common.contains(term));
    right.retain(|term| !common.contains(term));
    if left.len() == 1 && right.len() == 1 && complements(left[0], right[0]) {
        return Some((common, left[0]));
    }
    None
}

fn same_transition_effect(a: &Transition, b: &Transition) -> bool {
    a.target == b.target && a.consumes_step == b.consumes_step && a.rotations == b.rotations
}

// Merge equal effects before applying path conditions, so shared suffixes
// do not duplicate guards.
fn merge_branches(
    ctx: &mut Context,
    protocol: &mut ProtoGraph,
    symbols: &SymbolTable,
    branches: Vec<(ExprRef, Node)>,
) -> Node {
    let mut merged = Node::empty();
    for (_, branch) in &branches {
        for action in &branch.actions {
            if !merged
                .actions
                .iter()
                .any(|a| match (&protocol[a.op], &protocol[action.op]) {
                    (Op::Assign(a, _), Op::Assign(b, _)) => same_assignment_target(symbols, *a, *b),
                    (a, b) => a == b,
                })
            {
                merged.actions.push(action.clone());
            }
        }
        for edge in &branch.transitions {
            if !merged
                .transitions
                .iter()
                .any(|e| same_transition_effect(e, edge))
            {
                merged.transitions.push(edge.clone());
            }
        }
    }
    let conditions = branches.iter().map(|(g, _)| *g).collect::<Vec<_>>();
    for action in &mut merged.actions {
        if let Op::Assign(target, _) = protocol[action.op] {
            let mut assignments = Vec::new();
            for (condition, branch) in &branches {
                for a in &branch.actions {
                    if let Op::Assign(register, assignment) = &protocol[a.op]
                        && same_assignment_target(symbols, target, *register)
                    {
                        let assignment =
                            guard_assignment(ctx, protocol, assignment.clone(), *condition);
                        assignments.push(assignment);
                    }
                }
            }
            let assignment = merge_disjoint_assignments(ctx, protocol, assignments);
            action.op = protocol.o(Op::Assign(target, assignment));
            action.guard = ctx.get_true();
        } else {
            let guards = branches
                .iter()
                .map(|(_, branch)| {
                    branch.actions.iter().fold(ctx.get_false(), |g, a| {
                        if protocol[a.op] == protocol[action.op] {
                            protocol.or_guard(ctx, g, a.guard)
                        } else {
                            g
                        }
                    })
                })
                .collect::<Vec<_>>();
            action.guard = merge_branch_guards(ctx, protocol, &conditions, guards.into_iter());
        }
    }
    for edge in &mut merged.transitions {
        let guards = branches
            .iter()
            .map(|(_, branch)| {
                branch
                    .transitions
                    .iter()
                    .filter(|e| same_transition_effect(e, edge))
                    .fold(ctx.get_false(), |g, e| protocol.or_guard(ctx, g, e.guard))
            })
            .collect::<Vec<_>>();
        edge.guard = merge_branch_guards(ctx, protocol, &conditions, guards.into_iter());
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
    reads: &FxHashSet<ExprRef>,
    path: &mut BTreeSet<NodeId>,
) -> Node {
    path.insert(source);
    let node = sources[&source].clone();
    let values = assigned_values(ctx, protocol, symbols, &node.actions, reads);
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
        } else if path.contains(&edge.target) {
            let op = protocol.o(Op::InternalAssertFalse);
            Node {
                actions: vec![Action::new(ctx.get_true(), op)],
                transitions: vec![],
            }
        } else {
            let mut branch =
                contract_node(ctx, protocol, symbols, edge.target, sources, reads, path);
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
    use cranelift_entity::EntityRef;
    use patronus::expr::SerializableIrNode;

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
