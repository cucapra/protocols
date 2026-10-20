// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::symbol::SymbolTable;
use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::edge_contract::{merge_ordered_assignment, merge_unordered_assignment};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use itertools::Itertools;
use patronus::expr::{Context, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

/// Reaching assignments to DUT input pins, keyed by full port name.
/// Register and iterator values remain opaque inputs to these expressions.
pub type ReachingDefs = FxHashMap<String, Assignment>;

/// Nodes only store their outgoing transitions. This function precomputes and
/// returns the in-neighbors for each node.
use std::collections::VecDeque;

pub fn predecessors(pg: &ProtoGraph, start: NodeId) -> FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> {
    let mut predecessors: FxHashMap<NodeId, Vec<(NodeId, ExprRef)>> = FxHashMap::default();
    let mut visited: FxHashSet<NodeId> = FxHashSet::default();
    let mut queue: VecDeque<NodeId> = VecDeque::new();

    // Start BFS from the given node
    queue.push_back(start);
    visited.insert(start);

    while let Some(current_node) = queue.pop_front() {
        // For each transition from current node
        for t in pg[current_node].clone().transitions {
            let target = t.target;

            // Add predecessor relationship
            predecessors
                .entry(target)
                .or_default()
                .push((current_node, t.guard));

            // If we haven't visited this node yet, add it to queue
            if !visited.contains(&target) {
                visited.insert(target);
                queue.push_back(target);
            }
        }
    }

    predecessors
}

pub fn simplify_guard(ctx: &mut Context, pg: &mut ProtoGraph, guard: ExprRef) -> ExprRef {
    pg.simplifier.simplify(ctx, guard)
}

// TODO: I feel like this can be done at *merge-time* in edge-contract.rs instead
// TODO: of as a post-processing step
pub fn canonicalize_assignment(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    assignment: Assignment,
) -> Assignment {
    let dont_care = simplify_guard(ctx, pg, assignment.dont_care);
    if dont_care == ctx.get_true() {
        return Assignment {
            dont_care,
            concretes: Vec::new(),
        };
    }

    let mut prior = dont_care;
    let mut concretes: Vec<(ExprRef, ExprRef)> = Vec::new();

    for (guard, rhs) in assignment.concretes {
        let guard = simplify_guard(ctx, pg, guard);
        let not_prior = pg.not_guard(ctx, prior);
        let effective_guard = pg.and_guard(ctx, not_prior, guard);
        let effective_guard = simplify_guard(ctx, pg, effective_guard);

        match check_sat(ctx, pg, effective_guard) {
            SatResult::DefinitelyUnsat => {}
            SatResult::AlwaysSat => {
                merge_concrete_guard(ctx, pg, &mut concretes, ctx.get_true(), rhs);
                break;
            }
            SatResult::MaybeSat => {
                merge_concrete_guard(ctx, pg, &mut concretes, effective_guard, rhs);
                let next_prior = pg.or_guard(ctx, prior, effective_guard);
                prior = simplify_guard(ctx, pg, next_prior);
            }
        }

        if prior == ctx.get_true() {
            break;
        }
    }

    Assignment {
        dont_care,
        concretes,
    }
}

/// if the `rhs` already exists in `concretes` with guard `old_guard`
/// `guard` should be an *effective* guard, so that performing
/// `old_guard || guard` does not violate merge semantics
fn merge_concrete_guard(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    concretes: &mut Vec<(ExprRef, ExprRef)>,
    guard: ExprRef,
    rhs: ExprRef,
) {
    if let Some((existing_guard, _)) = concretes
        .iter_mut()
        .find(|(_, existing_rhs)| *existing_rhs == rhs)
    {
        let merged_guard = pg.or_guard(ctx, *existing_guard, guard);
        *existing_guard = simplify_guard(ctx, pg, merged_guard);
    } else {
        concretes.push((guard, rhs));
    }
}

/// An assignment is *total* when at least one of it's guards must trigger.
/// That is, `NOT(dc_guard OR concrete_g1 OR ... OR concrete_gn)` is not satisfiable.
pub fn assignment_is_total(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    assignment: &Assignment,
) -> bool {
    let coverage = assignment
        .concretes
        .iter()
        .fold(assignment.dont_care, |coverage, (guard, _)| {
            pg.or_guard(ctx, coverage, *guard)
        });

    match check_sat(ctx, pg, coverage) {
        SatResult::AlwaysSat => true,
        SatResult::DefinitelyUnsat | SatResult::MaybeSat => false,
    }
}

/// Take `branch_guard`, i.e. a guard on an assignment and simplify it to `Some(g)`
/// under the assumption that `transition_guard` is true. If returns `None`
/// then the branch can be removed.
pub fn restrict_branch_to_edge(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    branch_guard: ExprRef,
    transition_guard: ExprRef,
) -> Option<ExprRef> {
    let overlap = pg.and_guard(ctx, branch_guard, transition_guard);
    let overlap = simplify_guard(ctx, pg, overlap);

    // are `transition_guard` and `branch_guard` mutually exclusive?
    if matches!(check_sat(ctx, pg, overlap), SatResult::DefinitelyUnsat) {
        return None;
    }

    // does `transition_guard` imply `branch_guard`?
    // t => b == NOT t OR b == NOT(t AND not B). so check t AND not B is unsat.
    let not_branch = pg.not_guard(ctx, branch_guard);
    let transition_without_branch = pg.and_guard(ctx, transition_guard, not_branch);
    if matches!(
        check_sat(ctx, pg, transition_without_branch),
        SatResult::DefinitelyUnsat
    ) {
        return Some(ctx.get_true());
    }

    // can't simplify, so we have to return the overlap
    Some(overlap)
}

/// For each branch of `assignment`, rewrite it under the assumption that
/// `transition_guard` is true.
fn restrict_assignment_to_edge(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    assignment: Assignment,
    transition_guard: ExprRef,
) -> Assignment {
    let assignment = canonicalize_assignment(ctx, pg, assignment);
    let dont_care = restrict_branch_to_edge(ctx, pg, assignment.dont_care, transition_guard)
        .unwrap_or(ctx.get_false());
    let concretes = assignment
        .concretes
        .into_iter()
        .filter_map(|(guard, rhs)| {
            restrict_branch_to_edge(ctx, pg, guard, transition_guard).map(|guard| (guard, rhs))
        })
        .collect();

    canonicalize_assignment(
        ctx,
        pg,
        Assignment {
            dont_care,
            concretes,
        },
    )
}

/// Returns `true` if this assignment might produce multiple different values
fn has_multiple_outcomes(ctx: &mut Context, pg: &mut ProtoGraph, assignment: &Assignment) -> bool {
    let canonicalized = canonicalize_assignment(ctx, pg, assignment.clone());
    canonicalized.concretes.len() + usize::from(canonicalized.dont_care != ctx.get_false()) > 1
}

// the binary merge function for reaching definitions analysis is just `merge_unordered_assignment`
fn merge_assignment(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    existing: Assignment,
    new: Assignment,
) -> Assignment {
    let assignment = merge_unordered_assignment(ctx, pg, &mut None, existing, new);
    canonicalize_assignment(ctx, pg, assignment)
}

// the binary transfer function for reaching definitions analysis is just `merge_ordered_assignment`
fn transfer_assignment(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    existing: Assignment,
    assignment: Assignment,
) -> Assignment {
    let assignment = merge_ordered_assignment(ctx, pg, existing, assignment);
    canonicalize_assignment(ctx, pg, assignment)
}

pub fn reaching_definitions(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    st: &SymbolTable,
) -> FxHashMap<NodeId, ReachingDefs> {
    reaching_definitions_from(ctx, pg, st, pg.entry)
}

pub fn reaching_definitions_from(
    ctx: &mut Context,
    // TODO: it's a bit of a shame that we have to pass a mutable graph for an analysis,
    // but the simplifier inside of proto graph needs to be able to cache things
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    start: NodeId,
) -> FxHashMap<NodeId, ReachingDefs> {
    let preds = predecessors(pg, start);
    let mut in_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();
    let mut out_defs: FxHashMap<NodeId, ReachingDefs> = FxHashMap::default();

    // worklist by default is all reachable nodes.
    // let mut worklist: Vec<NodeId> = reachable.iter().copied().collect();
    let mut worklist: Vec<NodeId> = reachable_node_ids(ctx, pg, start);

    while let Some(id) = worklist.pop() {
        let mut merged = ReachingDefs::default();
        let mut incoming_conflicts = FxHashSet::default();
        for (pred_id, transition_guard) in preds.get(&id).into_iter().flatten() {
            if let Some(pred_defs) = out_defs.get(pred_id) {
                for (symbol_name, pred_assignment) in pred_defs {
                    let assignment = restrict_assignment_to_edge(
                        ctx,
                        pg,
                        pred_assignment.clone(),
                        *transition_guard,
                    );

                    // don't insert a reaching definition for a fully empty assignment
                    if assignment.dont_care == ctx.get_false() && assignment.concretes.is_empty() {
                        continue;
                    }

                    merged
                        .entry(symbol_name.clone())
                        .and_modify(|existing| {
                            *existing =
                                merge_assignment(ctx, pg, existing.clone(), assignment.clone());
                            if has_multiple_outcomes(ctx, pg, existing) {
                                incoming_conflicts.insert(symbol_name.clone());
                            }
                        })
                        .or_insert(assignment);
                }
            }
        }

        if id != start {
            in_defs.insert(id, merged);
        }

        let assignments = pg[id]
            .actions
            .iter()
            .filter_map(|a| match pg[a.op].clone() {
                Op::Assign(symbol_id, assignment) if st[symbol_id].is_in_port() => {
                    Some((symbol_id, assignment))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut out = in_defs.get(&id).cloned().unwrap_or_default();

        for (symbol_id, assignment) in assignments {
            let key = st.full_name_from_symbol_id(&symbol_id).to_string();
            let existing = out.remove(&key).unwrap_or_else(|| Assignment {
                dont_care: ctx.get_false(),
                concretes: Vec::new(),
            });
            incoming_conflicts.remove(&key);
            out.insert(key, transfer_assignment(ctx, pg, existing, assignment));
        }

        assert!(
            incoming_conflicts.is_empty(),
            "reaching definition conflict remains after transfer at {id}"
        );

        if out_defs.get(&id) != Some(&out) {
            out_defs.insert(id, out);

            worklist.extend(
                pg[id]
                    .clone()
                    .transitions
                    .into_iter()
                    .map(|t| t.target)
                    .unique(),
            );
        }
    }

    out_defs
}

pub fn format_reaching_defs(
    ctx: &Context,
    protocol: &ProtoGraph,
    _symbols: &SymbolTable,
    reaching_defs: &FxHashMap<NodeId, ReachingDefs>,
) -> String {
    let mut out = String::new();
    let mut node_ids = reaching_defs.keys().copied().collect::<Vec<_>>();
    node_ids.sort();

    for node_id in node_ids {
        out.push_str(&format!("{node_id}:\n"));
        let Some(defs) = reaching_defs.get(&node_id) else {
            continue;
        };

        let mut symbol_defs = defs.iter().collect::<Vec<_>>();
        symbol_defs.sort_by_key(|(symbol_name, _)| *symbol_name);

        for (symbol_name, assignment) in symbol_defs {
            out.push_str(&format!(
                "  {}: {}\n",
                symbol_name,
                format_assignment(ctx, protocol, assignment),
            ));
        }
    }

    out
}

fn format_assignment(ctx: &Context, protocol: &ProtoGraph, assignment: &Assignment) -> String {
    let mut parts = Vec::new();
    if assignment.dont_care != ctx.get_false() {
        parts.push(format!(
            "X if {}",
            crate::ir::graphviz::format_expr(ctx, protocol, assignment.dont_care)
        ));
    }
    for (guard, rhs) in &assignment.concretes {
        parts.push(format!(
            "{} if {}",
            crate::ir::graphviz::format_expr(ctx, protocol, *rhs),
            crate::ir::graphviz::format_expr(ctx, protocol, *guard)
        ));
    }
    if parts.is_empty() {
        "internal_assert_false".to_string()
    } else {
        parts.join("; ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::ROOT_SCOPE;

    fn test_graph() -> ProtoGraph {
        ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE))
    }

    fn concrete_assignment(ctx: &Context, guard: ExprRef, rhs: ExprRef) -> Assignment {
        Assignment::concrete(ctx.get_false(), guard, rhs)
    }

    #[test]
    fn dut_input_dataflow_preserves_loop_state() {
        use crate::frontend;
        use crate::frontend::diagnostic::DiagnosticHandler;
        use crate::frontend::require_single_module;
        use crate::ir::lowering::lower_ast_to_ir;
        use crate::ir::propagate_assigns::propagate_assignments;
        use crate::ir::proto_graph::{Action, Node, Transition};
        use cranelift_entity::PrimaryMap;
        use patronus::expr::TypeCheck;

        let filename = "../tests/loops/loops.prot";
        let mut handler = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[filename], &mut handler, false, false).unwrap();
        let module = require_single_module(modules, &[filename]).unwrap();
        let ast = module
            .protos
            .into_iter()
            .find(|p| p.name == "for_distinct")
            .unwrap();
        let mut ctx = Context::default();
        let mut graph = lower_ast_to_ir(&mut ctx, ast, &mut symbols);
        let state_actions = graph
            .nodes()
            .flat_map(|(_, node)| &node.actions)
            .filter(|a| match graph[a.op] {
                Op::Assign(target, _) => !symbols[target].is_in_port(),
                Op::Data { .. } | Op::Last { .. } | Op::Valid { .. } => true,
                _ => false,
            })
            .cloned()
            .collect::<Vec<_>>();
        let inputs = graph.dut_input_symbols(&symbols).collect::<Vec<_>>();
        let mut assignments = Vec::new();
        for pin in inputs {
            // State references in a DUT RHS are opaque: the analysis must not
            // import or substitute the assignments that update that state.
            let width = match symbols[pin].tpe() {
                crate::frontend::symbol::Type::BitVec(width) => width,
                _ => unreachable!(),
            };
            let rhs = *graph
                .register_inputs
                .values()
                .find(|expr| expr.get_bv_type(&ctx) == Some(width))
                .unwrap();
            let assignment = Assignment::concrete(ctx.get_false(), ctx.get_true(), rhs);
            let op = graph.o(Op::Assign(pin, assignment.clone()));
            assignments.push((pin, assignment, Action::new(ctx.get_true(), op)));
        }
        let mut nodes = PrimaryMap::new();
        let entry = nodes.push(Node::empty());
        let body = nodes.push(Node::empty());
        nodes[entry].actions = assignments
            .iter()
            .map(|(_, _, action)| action.clone())
            .collect();
        nodes[entry].transitions = vec![Transition::new(ctx.get_true(), body, true)];
        nodes[body].actions = state_actions.clone();
        // One pin is assigned locally; the other must be propagated from entry.
        nodes[body].actions.push(assignments[0].2.clone());
        nodes[body].transitions = vec![Transition::new(ctx.get_true(), body, true)];
        graph = graph.with_nodes(nodes, entry);

        let definitions = reaching_definitions(&mut ctx, &mut graph, &symbols);
        let input_names = assignments
            .iter()
            .map(|(pin, _, _)| symbols.full_name_from_symbol_id(pin))
            .collect::<Vec<_>>();
        for defs in definitions.values() {
            assert_eq!(defs.len(), input_names.len());
            assert!(defs.keys().all(|name| input_names.contains(name)));
        }
        propagate_assignments(&mut ctx, &mut graph, &symbols, &definitions);
        let preserved = graph[body]
            .actions
            .iter()
            .filter(|a| !matches!(graph[a.op], Op::Assign(pin, _) if symbols[pin].is_in_port()))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(preserved, state_actions);
        for (pin, expected, _) in assignments {
            let actual = graph[body]
                .actions
                .iter()
                .filter_map(|a| match &graph[a.op] {
                    Op::Assign(target, assignment) if *target == pin => Some(assignment),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(actual, vec![&expected]);
        }
    }

    #[test]
    fn merge_flags_multiple_reaching_concretes_even_when_guards_are_exclusive() {
        let mut pg = test_graph();
        let mut ctx = Context::default();
        let p = ctx.bv_symbol("p", 1);
        let not_p = pg.not_guard(&mut ctx, p);
        let one = ctx.bv_symbol("one", 1);
        let zero = ctx.bv_symbol("zero", 1);

        let from_a = concrete_assignment(&ctx, p, one);
        let from_b = concrete_assignment(&ctx, not_p, zero);

        let merged = merge_assignment(&mut ctx, &mut pg, from_a, from_b);

        assert!(has_multiple_outcomes(&mut ctx, &mut pg, &merged));
        assert_eq!(merged.dont_care, ctx.get_false());
        assert_eq!(merged.concretes.len(), 2);
    }

    #[test]
    fn merge_flags_maybe_overlapping_reaching_definitions() {
        let mut pg = test_graph();
        let mut ctx = Context::default();
        let p = ctx.bv_symbol("p", 1);
        let q = ctx.bv_symbol("q", 1);
        let one = ctx.bv_symbol("one", 1);
        let zero = ctx.bv_symbol("zero", 1);

        let from_a = concrete_assignment(&ctx, p, one);
        let from_b = concrete_assignment(&ctx, q, zero);

        let merged = merge_assignment(&mut ctx, &mut pg, from_a, from_b);

        assert!(has_multiple_outcomes(&mut ctx, &mut pg, &merged));
        assert_eq!(merged.dont_care, ctx.get_false());
        assert_eq!(merged.concretes.len(), 2);
    }

    #[test]
    fn total_assignment_kills_incoming_reaching_definition_conflict() {
        let mut pg = test_graph();
        let mut ctx = Context::default();
        let p = ctx.bv_symbol("p", 1);
        let q = ctx.bv_symbol("q", 1);
        let one = ctx.bv_symbol("one", 1);
        let zero = ctx.bv_symbol("zero", 1);
        let two = ctx.bv_symbol("two", 1);

        let from_a = concrete_assignment(&ctx, p, one);
        let from_b = concrete_assignment(&ctx, q, zero);
        let conflicted = merge_assignment(&mut ctx, &mut pg, from_a, from_b);
        assert!(has_multiple_outcomes(&mut ctx, &mut pg, &conflicted));

        let reassignment = concrete_assignment(&ctx, ctx.get_true(), two);
        let transferred = transfer_assignment(&mut ctx, &mut pg, conflicted, reassignment);

        assert!(assignment_is_total(&mut ctx, &mut pg, &transferred));
    }
}
