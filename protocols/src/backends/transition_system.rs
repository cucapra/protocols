use crate::PortId;
use crate::frontend::symbol;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::proto_graph::{Assignment, NodeId, Op, ProtoGraph};
use baa::WidthInt;
use itertools::Itertools;
use patronus::expr::{Context, ExprRef, Type, simple_transform_expr};
use patronus::system::{State, TransitionSystem};
use rustc_hash::{FxHashMap, FxHashSet};
use std::borrow::Cow;

/// the first part of an ITE: the if condition, and the then expression
pub struct IfThenExpr {
    pub if_cond: ExprRef,
    pub then: ExprRef,
}

struct InputDriver {
    port: PortId,
    input_expr_ref: ExprRef,
    /// the port's value expression
    input_ite: ExprRef,
    /// the condition under which the input resolved to DontCare
    /// this is used for pretty printing the ASCII waveform
    input_is_dont_care: ExprRef,
    /// The corresponding input to the transition system, invoked on a DontCare assignment
    input_dont_care: ExprRef,
}

/// Turn a vector of `IfThenExpr`s, with *Right-to-Left* priority, into an ITE with default `default`
pub(crate) fn if_thens_to_ite(v: Vec<IfThenExpr>, ctx: &mut Context, default: ExprRef) -> ExprRef {
    let mut ite = default;

    for ge in v {
        ite = ctx.ite(ge.if_cond, ge.then, ite);
    }

    ite
}

fn assignment_to_ite(
    a: Assignment,
    ctx: &mut Context,
    dont_care: ExprRef,
    default: ExprRef,
) -> ExprRef {
    let mut ite = default;

    for (guard, expr) in a.concretes {
        ite = ctx.ite(guard, expr, ite);
    }

    ite = ctx.ite(a.dont_care, dont_care, ite);

    ite
}

/// return an expression which is `true` iff some branch of `Assignment` `a` triggers
fn assignment_is_triggered(a: &Assignment, ctx: &mut Context) -> ExprRef {
    a.concretes
        .iter()
        .fold(a.dont_care, |acc, (guard, _)| ctx.or(acc, *guard))
}

fn replace_expr(ctx: &mut Context, expr: ExprRef, old_expr: ExprRef, new_expr: ExprRef) -> ExprRef {
    simple_transform_expr(ctx, expr, |_ctx, candidate, _children| {
        (candidate == old_expr).then_some(new_expr)
    })
}

fn replace_expr_uses(
    ts: &mut TransitionSystem,
    ctx: &mut Context,
    old_expr: ExprRef,
    new_expr: ExprRef,
) {
    let mut replace = |expr| replace_expr(ctx, expr, old_expr, new_expr);

    for constraint in &mut ts.constraints {
        *constraint = replace(*constraint);
    }

    for bad_state in &mut ts.bad_states {
        *bad_state = replace(*bad_state);
    }

    for output in &mut ts.outputs {
        output.expr = replace(output.expr);
    }

    for state in &mut ts.states {
        state.init = state.init.map(&mut replace);
        state.next = state.next.map(&mut replace);
    }
}

fn replace_proto_graph_exprs(
    pg: &mut ProtoGraph,
    ctx: &mut Context,
    old_expr: ExprRef,
    new_expr: ExprRef,
) {
    for (_, node) in pg.nodes_mut() {
        for action in &mut node.actions {
            action.guard = replace_expr(ctx, action.guard, old_expr, new_expr);
        }

        for transition in &mut node.transitions {
            transition.guard = replace_expr(ctx, transition.guard, old_expr, new_expr);
        }
    }

    for (_, op) in pg.ops_mut() {
        match op {
            Op::Assign(_, assignment) => {
                assignment.dont_care = replace_expr(ctx, assignment.dont_care, old_expr, new_expr);
                for (guard, rhs) in &mut assignment.concretes {
                    *guard = replace_expr(ctx, *guard, old_expr, new_expr);
                    *rhs = replace_expr(ctx, *rhs, old_expr, new_expr);
                }
            }
            Op::AssertEq(lhs, rhs) => {
                *lhs = replace_expr(ctx, *lhs, old_expr, new_expr);
                *rhs = replace_expr(ctx, *rhs, old_expr, new_expr);
            }
            Op::Fork | Op::InternalAssertFalse | Op::Done => {}
        }
    }

    for expr in pg.symbol_expr.values_mut() {
        *expr = replace_expr(ctx, *expr, old_expr, new_expr);
    }

    let dont_cares = std::mem::take(&mut pg.dont_cares);
    pg.dont_cares = dont_cares
        .into_iter()
        .map(|expr| replace_expr(ctx, expr, old_expr, new_expr))
        .collect();
}

/// swap out all the ports in the ProtoGraph with their equivalents
/// in the DUT
fn bind_proto_graph_ports_to_dut(
    pg: &mut ProtoGraph,
    ctx: &mut Context,
    symbol_to_port: &FxHashMap<SymbolId, PortId>,
    port_to_expr: &FxHashMap<PortId, ExprRef>,
) {
    let port_bindings: Vec<_> = pg
        .symbol_expr
        .iter()
        .filter_map(|(symbol_id, graph_expr)| {
            let port = symbol_to_port.get(symbol_id)?;
            let dut_expr = port_to_expr.get(port)?;
            Some((*graph_expr, *dut_expr))
        })
        .filter(|(graph_expr, dut_expr)| graph_expr != dut_expr)
        .collect();

    for (graph_expr, dut_expr) in port_bindings {
        replace_proto_graph_exprs(pg, ctx, graph_expr, dut_expr);
    }
}

pub struct LoweredSystemResult {
    pub ctx: Context,
    pub ts: TransitionSystem,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub node_symbol: ExprRef,
    pub done_state: Option<ExprRef>,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
}

pub(crate) struct CoreLoweredSystem {
    pub ctx: Context,
    pub ts: TransitionSystem,
    pub pg: ProtoGraph,
    pub port_to_expr: FxHashMap<PortId, ExprRef>,
    pub node_symbol: ExprRef,
    pub node_id_width: u64,
    pub done_state: ExprRef,
    pub external_assert_state: ExprRef,
    pub internal_assert_state: ExprRef,
    pub is_dont_care: FxHashMap<PortId, ExprRef>,
    pub reachable_nodes: Vec<NodeId>,
}

pub(crate) fn lower_proto_graph_to_transition_system(
    mut pg: ProtoGraph,
    mut ctx: Context,
    mut ts: TransitionSystem,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    mut port_to_expr: FxHashMap<PortId, ExprRef>,
    st: &SymbolTable,
) -> CoreLoweredSystem {
    let mut is_dont_care = FxHashMap::default();
    for &dont_care in &pg.dont_cares {
        ts.add_input(&ctx, dont_care);
    }
    bind_proto_graph_ports_to_dut(&mut pg, &mut ctx, &symbol_to_port, &port_to_expr);

    let node_count = pg.nodes().try_len().unwrap() as u64 + 3;
    let node_id_width = u64::from(u64::BITS - node_count.leading_zeros());

    let s = ctx.string(Cow::from("node"));
    let node_sym = ctx.symbol(s, Type::BV(node_id_width as WidthInt));

    // the initial node state is the entry
    let entry_id = ctx.bit_vec_val(pg.entry.as_u32(), node_id_width);
    let external_bad_state_id = ctx.bit_vec_val(pg.next_node_id().as_u32(), node_id_width);

    // TODO: is it safe to assume node ids are monotone?
    let internal_bad_state_id = ctx.bit_vec_val(pg.next_node_id().as_u32() + 1, node_id_width);
    let done_state_id = ctx.bit_vec_val(pg.next_node_id().as_u32() + 2, node_id_width);

    // Generate a big vector of all the transitions
    let mut transitions: Vec<IfThenExpr> = vec![];
    // create the transition function - only use the reachable nodes for efficiency
    let mut q = vec![pg.entry];
    let mut visited: FxHashSet<NodeId> = FxHashSet::default();
    visited.insert(pg.entry);
    let mut reachable_nodes = Vec::new();
    while let Some(id) = q.pop() {
        reachable_nodes.push(id);
        let src = ctx.bit_vec_val(id.as_u32(), node_id_width);
        let node_guard = ctx.equal(node_sym, src);

        // Done has lower priority than graph transitions. Since later ITE arms
        // win, emit done transitions before normal transitions.
        for action in &pg[id].actions {
            if matches!(pg[action.op], Op::Done) {
                let done_guard = ctx.and(node_guard, action.guard);
                transitions.push(IfThenExpr {
                    if_cond: done_guard,
                    then: done_state_id,
                });
            }
        }

        for (guard, dst_node) in pg[id].transitions.iter().map(|t| (t.guard, t.target)) {
            let dst = ctx.bit_vec_val(dst_node.as_u32(), node_id_width);

            // node_sym == src && guard
            let and_guard = ctx.and(node_guard, guard);

            let t = IfThenExpr {
                if_cond: and_guard,
                then: dst,
            };
            transitions.push(t);

            if !visited.contains(&dst_node) {
                visited.insert(dst_node);
                q.push(dst_node);
            }
        }

        // these need to come later in the vector so they are preferred in the ITE
        // i.e. assertions are checked before transitions
        for action in &pg[id].actions {
            match pg[action.op].clone() {
                Op::AssertEq(lhs, rhs) => {
                    let eq = ctx.equal(lhs, rhs);
                    let assertion_failed = ctx.not(eq);
                    let action_guard = ctx.and(action.guard, assertion_failed);
                    let bad_guard = ctx.and(node_guard, action_guard);
                    transitions.push(IfThenExpr {
                        if_cond: bad_guard,
                        then: external_bad_state_id,
                    });
                }
                Op::InternalAssertFalse => {
                    let bad_guard = ctx.and(node_guard, action.guard);
                    transitions.push(IfThenExpr {
                        if_cond: bad_guard,
                        then: internal_bad_state_id,
                    });
                }
                Op::Assign(_, _) | Op::Fork | Op::Done => {}
            }
        }
    }

    let done_state_guard = ctx.equal(node_sym, done_state_id);
    transitions.push(IfThenExpr {
        if_cond: done_state_guard,
        then: done_state_id,
    });
    let external_bad_state_guard = ctx.equal(node_sym, external_bad_state_id);
    transitions.push(IfThenExpr {
        if_cond: external_bad_state_guard,
        then: external_bad_state_id,
    });
    let internal_bad_state_guard = ctx.equal(node_sym, internal_bad_state_id);
    transitions.push(IfThenExpr {
        if_cond: internal_bad_state_guard,
        then: internal_bad_state_id,
    });

    // if no transition is satisfied, we go to the internal bad state
    // the final done state self-loops, so it won't trigger this
    let mut transition_ite = if_thens_to_ite(transitions, &mut ctx, internal_bad_state_id);

    // set up ITE expressions based on what node state we're in for each port,
    // and replace the inputs with the ITEs everywhere
    let input_symbols: Vec<SymbolId> = pg.proto_ctx.dut_input_symbols(st).collect();

    // set up default input drivers per input
    let mut input_drivers = Vec::with_capacity(input_symbols.len());
    for input in input_symbols {
        let tpe = st[input].tpe();
        let input_width = match tpe {
            symbol::Type::BitVec(width) => width,
            _ => panic!("unsupported input port type"),
        };

        let dont_care_name = format!("dont_care.{}", st.full_name_from_symbol_id(&input));
        let input_dont_care = ctx.bv_symbol(&dont_care_name, input_width as WidthInt);
        ts.add_input(&ctx, input_dont_care);

        let input_port = *symbol_to_port.get(&input).unwrap();
        let input_expr_ref = *port_to_expr.get(&input_port).unwrap();
        input_drivers.push((
            input,
            InputDriver {
                port: input_port,
                input_expr_ref,
                input_ite: input_dont_care,
                input_is_dont_care: ctx.get_true(),
                input_dont_care,
            },
        ));
    }

    // populate the input drivers with assignments in the reachable nodes
    for (input, driver) in &mut input_drivers {
        let mut assignment_failed_guard = ctx.get_false();
        let mut grouped_assignments: Vec<(Assignment, ExprRef)> = Vec::new();

        for id in &reachable_nodes {
            let node_id_expr = ctx.bit_vec_val(id.as_u32(), node_id_width);
            let node_equals = ctx.equal(node_sym, node_id_expr);

            let assignment: Assignment = pg[*id]
                .actions
                .iter()
                .filter_map(|action| match pg[action.op].clone() {
                    Op::Assign(assigned_input, expr) if assigned_input == *input => Some(expr),
                    _ => None,
                })
                .next()
                .unwrap();

            let assignment_is_triggered = assignment_is_triggered(&assignment, &mut ctx);
            let assignment_not_triggered = ctx.not(assignment_is_triggered);

            // if an assignment isn't triggered, go to the bad state
            let input_assignment_failed = ctx.and(node_equals, assignment_not_triggered);
            assignment_failed_guard = ctx.or(assignment_failed_guard, input_assignment_failed);

            if let Some((_, group_guard)) = grouped_assignments
                .iter_mut()
                .find(|(grouped_assignment, _)| *grouped_assignment == assignment)
            {
                *group_guard = ctx.or(*group_guard, node_equals);
            } else {
                grouped_assignments.push((assignment, node_equals));
            }
        }

        if assignment_failed_guard != ctx.get_false() {
            transition_ite = ctx.ite(
                assignment_failed_guard,
                internal_bad_state_id,
                transition_ite,
            );
        }

        for (assignment, group_guard) in grouped_assignments {
            let assignment_is_dont_care = assignment.dont_care;
            let assignment_ite = assignment_to_ite(
                assignment,
                &mut ctx,
                driver.input_dont_care,
                driver.input_expr_ref,
            );

            driver.input_ite = ctx.ite(group_guard, assignment_ite, driver.input_ite);
            driver.input_is_dont_care = ctx.ite(
                group_guard,
                assignment_is_dont_care,
                driver.input_is_dont_care,
            );
        }
    }

    // replace the input ExprRef with the input_ite everywhere
    for (_, driver) in input_drivers {
        replace_expr_uses(&mut ts, &mut ctx, driver.input_expr_ref, driver.input_ite);
        transition_ite = replace_expr(
            &mut ctx,
            transition_ite,
            driver.input_expr_ref,
            driver.input_ite,
        );
        for expr in port_to_expr.values_mut() {
            *expr = replace_expr(&mut ctx, *expr, driver.input_expr_ref, driver.input_ite);
        }
        is_dont_care.insert(driver.port, driver.input_is_dont_care);
    }

    let node_state = State {
        symbol: node_sym,
        init: Some(entry_id),
        next: Some(transition_ite),
    };
    ts.add_state(&ctx, node_state);

    CoreLoweredSystem {
        ctx,
        ts,
        pg,
        port_to_expr,
        node_symbol: node_sym,
        node_id_width,
        done_state: done_state_id,
        external_assert_state: external_bad_state_id,
        internal_assert_state: internal_bad_state_id,
        is_dont_care,
        reachable_nodes,
    }
}

pub fn into_transition_system(
    mut pg: ProtoGraph,
    ts: TransitionSystem,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    st: &SymbolTable,
) -> LoweredSystemResult {
    let ctx = std::mem::take(&mut pg.expr_ctx);
    let core =
        lower_proto_graph_to_transition_system(pg, ctx, ts, symbol_to_port, port_to_expr, st);

    LoweredSystemResult {
        ctx: core.ctx,
        ts: core.ts,
        port_to_expr: core.port_to_expr,
        node_symbol: core.node_symbol,
        done_state: Some(core.done_state),
        external_assert_state: core.external_assert_state,
        internal_assert_state: core.internal_assert_state,
        is_dont_care: core.is_dont_care,
    }
}
