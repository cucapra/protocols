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

struct GuardedExpr {
    pub guard: ExprRef,
    pub expr: ExprRef,
}

fn guard_exprs_to_ite(v: Vec<GuardedExpr>, ctx: &mut Context, default: ExprRef) -> ExprRef {
    let mut ite = default;

    for ge in v {
        ite = ctx.ite(ge.guard, ge.expr, ite);
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

pub fn into_transition_system(
    mut pg: ProtoGraph,
    mut ts: TransitionSystem,
    symbol_to_port: FxHashMap<SymbolId, PortId>,
    port_to_expr: FxHashMap<PortId, ExprRef>,
    st: &SymbolTable,
) -> (
    patronus::expr::Context,
    TransitionSystem,
    FxHashMap<PortId, ExprRef>,
) {
    let mut ctx = std::mem::take(&mut pg.expr_ctx);
    let mut port_to_expr = port_to_expr;
    bind_proto_graph_ports_to_dut(&mut pg, &mut ctx, &symbol_to_port, &port_to_expr);

    let node_count = pg.nodes().try_len().unwrap() as u64;
    let node_id_width = u64::from(u64::BITS - node_count.leading_zeros());

    let s = ctx.string(Cow::from("node"));
    let node_sym = ctx.symbol(s, Type::BV(node_id_width as WidthInt));

    // the initial node state is the entry
    let entry_id = ctx.bit_vec_val(pg.entry.as_u32(), node_id_width);
    let bad_state_id = ctx.bit_vec_val(pg.next_node_id().as_u32(), node_id_width);

    let mut transitions: Vec<GuardedExpr> = vec![];
    // create the transition function - only use the reachable nodes for efficiency
    let mut q = vec![pg.entry];
    let mut visited: FxHashSet<NodeId> = FxHashSet::default();
    visited.insert(pg.entry);
    while let Some(id) = q.pop() {
        let src = ctx.bit_vec_val(id.as_u32(), node_id_width);
        for (guard, dst_node) in pg[id].transitions.iter().map(|t| (t.guard, t.target)) {
            let dst = ctx.bit_vec_val(dst_node.as_u32(), node_id_width);

            // node_sym == src
            let node_guard = ctx.equal(node_sym, src);
            // node_sym == src && guard
            let and_guard = ctx.and(node_guard, guard);

            let t = GuardedExpr {
                guard: and_guard,
                expr: dst,
            };
            transitions.push(t);

            if !visited.contains(&dst_node) {
                visited.insert(dst_node);
                q.push(dst_node);
            }
        }
    }

    // TODO: ITE form is only equivalent if transition guards out of a node are mutually exclusive
    let transition_ite = guard_exprs_to_ite(transitions, &mut ctx, bad_state_id);
    // add the "node" state and the transition function for it
    let node_state = State {
        symbol: node_sym,
        init: Some(entry_id),
        next: Some(transition_ite),
    };

    // set up ITE expressions based on what node state we're in for each port,
    // and replace the inputs with the ITEs everywhere
    // TODO: is this the correct way to get ports here
    let input_symbols: Vec<SymbolId> = st
        .get_children(&pg.proto_ctx.type_param.unwrap())
        .into_iter()
        .filter(|sym_id| st[*sym_id].is_in_port())
        .collect();

    // TODO: this can be done as a single pass over nodes, instead of two loops
    for input in input_symbols.clone() {
        let tpe = st[input].tpe();
        let input_width = match tpe {
            symbol::Type::BitVec(width) => width,
            _ => panic!("unsupported input port type"),
        };

        let dont_care_name = format!("dont_care.{}", st.full_name_from_symbol_id(&input));
        let input_dont_care = ctx.bv_symbol(&dont_care_name, input_width as WidthInt);
        ts.add_input(&ctx, input_dont_care);

        // TODO: idk what to make the default. right now just the dont care?
        let mut input_ite = input_dont_care;
        // TODO: This iteration is unwieldy
        for id in visited.clone().drain() {
            let assignment: Assignment = pg[id]
                .actions
                .iter()
                .filter_map(|action| match pg[action.op].clone() {
                    Op::Assign(assigned_input, expr) if assigned_input == input => Some(expr),
                    _ => None,
                })
                .next()
                .unwrap();

            let assignment_ite= assignment_to_ite(
                assignment,
                &mut ctx,
                input_dont_care.clone(),
                input_dont_care.clone(),
            );

            let node_id_expr = ctx.bit_vec_val(id.as_u32(), node_id_width);
            let node_equals = ctx.equal(node_sym, node_id_expr);

            input_ite = ctx.ite(node_equals, assignment_ite, input_ite);
        }

        // replace the input ExprRef with the input_ite everywhere
        let input_expr_ref = *port_to_expr.get(symbol_to_port.get(&input).unwrap()).unwrap();
        replace_expr_uses(&mut ts, &mut ctx, input_expr_ref, input_ite);
        for expr in port_to_expr.values_mut() {
            *expr = replace_expr(&mut ctx, *expr, input_expr_ref, input_ite);
        }
    }

    ts.add_state(&ctx, node_state);
    (ctx, ts, port_to_expr)
}
