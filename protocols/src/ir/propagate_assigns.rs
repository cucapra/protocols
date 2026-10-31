use crate::frontend::symbol::{SymbolKind, SymbolTable};
use crate::ir::edge_contract::{raw_concrete_coverage, same_assignment_target};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::register_simplify::{RegisterFacts, simplify_registers};
use patronus::expr::{Context, find_symbols};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn insert_assignment_registers(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    st: &mut SymbolTable,
    entry: NodeId,
) -> RegisterFacts {
    let pins = pg.proto_ctx.dut_input_symbols(st).collect::<Vec<_>>();
    let mut initial = FxHashMap::default();
    let mut saved = Vec::new();
    for pin in pins {
        let name = st[pin].name().to_string();
        let value = pg.add_register(
            ctx,
            st,
            &format!("$previous_{name}"),
            st[pin].tpe().bitwidth(),
        );
        let released = pg.add_register(ctx, st, &format!("$previous_{name}_is_x"), 1);
        initial.insert(value, ctx.zero(st[pin].tpe().bitwidth()));
        initial.insert(released, ctx.get_true());
        saved.push((pin, value, released));
    }
    let nodes = pg.reachable_node_ids(ctx, entry);
    let step_entries = nodes
        .iter()
        .flat_map(|&node| &pg[node].transitions)
        .filter(|edge| edge.consumes_step)
        .map(|edge| edge.target)
        .collect::<FxHashSet<_>>();

    // Restore held inputs immediately after each step, before the next source statement
    for &node in &step_entries {
        assert!(
            pg[node].actions.is_empty(),
            "step targets must be empty restore nodes"
        );
        for &(pin, value, released) in &saved {
            let old_value = pg.symbol_expr(value).unwrap();
            let old_x = pg.symbol_expr(released).unwrap();
            let concrete = pg.not_guard(ctx, old_x);
            let op = pg.o(Op::Assign(
                pin,
                Assignment::concrete(old_x, concrete, old_value),
            ));
            pg.push_action(node, Action::new(ctx.get_true(), op));
        }
    }

    // mirror source writes into saved state
    for node in nodes {
        if step_entries.contains(&node) {
            continue;
        }
        let mut actions = Vec::new();
        for action in pg[node].actions.clone() {
            actions.push(action.clone());
            let Op::Assign(pin, assignment) = pg[action.op].clone() else {
                continue;
            };
            let Some(&(target, value, released)) = saved
                .iter()
                .find(|&&(p, _, _)| same_assignment_target(st, p, pin))
            else {
                continue;
            };
            assert_eq!(action.guard, ctx.get_true());
            // Protocol copies use distinct symbol IDs for the same physical input.
            if target != pin {
                actions.last_mut().unwrap().op = pg.o(Op::Assign(target, assignment.clone()));
            }
            let old_value = pg.symbol_expr(value).unwrap();
            let old_x = pg.symbol_expr(released).unwrap();
            let next_value = assignment.to_expr(ctx, old_value, old_value);
            let concrete = raw_concrete_coverage(ctx, pg, &assignment);
            let next_x = ctx.ite(concrete, ctx.get_false(), old_x);
            let next_x = ctx.ite(assignment.dont_care, ctx.get_true(), next_x);
            for (target, rhs) in [(value, next_value), (released, next_x)] {
                let op = pg.o(Op::Assign(
                    target,
                    Assignment::concrete(ctx.get_false(), ctx.get_true(), rhs),
                ));
                actions.push(Action::new(ctx.get_true(), op));
            }
        }
        pg.node_mut(node).actions = actions;
    }
    if !pg.loops.is_empty() {
        pg.register_inits
            .extend(initial.iter().map(|(&r, &v)| (r, v)));
    }
    initial
}

pub fn simplify_assignments(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    initial: &RegisterFacts,
) {
    let entry = pg.entry;
    simplify_assignments_from(ctx, pg, st, entry, initial);
}

pub fn simplify_assignments_from(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    st: &SymbolTable,
    entry: NodeId,
    initial: &RegisterFacts,
) {
    let preserved = FxHashSet::default();
    // Existing loop registers remain opaque storage anchors. Analyze the
    // inserted pin-history registers without specializing the first iteration.
    let dead = simplify_registers(ctx, pg, st, entry, initial, &preserved);
    pg.register_inits.retain(|r, _| !dead.contains(r));
    pg.simplify_all_exprs(ctx);
    if !pg.loops.is_empty() {
        return;
    }

    // Panic if there are any registers left.
    let mut expressions = Vec::new();
    for node in pg.reachable_node_ids(ctx, entry) {
        expressions.extend(pg[node].transitions.iter().map(|e| e.guard));
        for action in &pg[node].actions {
            expressions.push(action.guard);
            match &pg[action.op] {
                Op::Assign(target, a) => {
                    if st[*target].kind() == SymbolKind::AutomatonState {
                        expressions.push(pg.symbol_expr(*target).unwrap());
                    }
                    expressions.push(a.dont_care);
                    expressions.extend(a.concretes.iter().flat_map(|&(g, rhs)| [g, rhs]));
                }
                Op::AssertEq(a, b) => expressions.extend([*a, *b]),
                _ => {}
            }
        }
    }
    let used = expressions
        .into_iter()
        .flat_map(|e| find_symbols(ctx, e))
        .collect::<FxHashSet<_>>();
    let remaining = pg
        .symbol_expr
        .iter()
        .filter(|(r, expr)| st[**r].kind() == SymbolKind::AutomatonState && used.contains(expr))
        .map(|(r, _)| st[*r].full_name(st))
        .collect::<Vec<_>>();
    assert!(
        remaining.is_empty(),
        "we were unable to optimize away all register state: {remaining:?}"
    );
}
