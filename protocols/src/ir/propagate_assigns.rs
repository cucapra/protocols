use crate::frontend::symbol::{SymbolKind, SymbolTable};
use crate::ir::edge_contract::{
    merge_ordered_assignment, raw_concrete_coverage, same_assignment_target,
};
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
    for node in pg.reachable_node_ids(ctx, entry) {
        let mut actions = pg[node]
            .actions
            .iter()
            .filter(|a| !matches!(pg[a.op], Op::Assign(pin, _) if st[pin].is_in_port()))
            .cloned()
            .collect::<Vec<_>>();
        for &(pin, value, released) in &saved {
            let mut local = Assignment {
                dont_care: ctx.get_false(),
                concretes: vec![],
            };
            for action in pg[node].actions.clone() {
                if let Op::Assign(target, assignment) = pg[action.op].clone()
                    && same_assignment_target(st, pin, target)
                {
                    assert_eq!(
                        action.guard,
                        ctx.get_true(),
                        "assignment action guards must be true"
                    );
                    local = merge_ordered_assignment(ctx, pg, local, assignment);
                }
            }
            let old_value = pg.symbol_expr(value).unwrap();
            let old_x = pg.symbol_expr(released).unwrap();
            let concrete_guard = raw_concrete_coverage(ctx, pg, &local);
            let coverage = pg.or_guard(ctx, local.dont_care, concrete_guard);
            let missing = pg.not_guard(ctx, coverage);
            let held_x = pg.and_guard(ctx, missing, old_x);
            let dont_care = pg.or_guard(ctx, local.dont_care, held_x);
            let not_x = pg.not_guard(ctx, old_x);
            let held_value_guard = pg.and_guard(ctx, missing, not_x);
            let mut concrete = local.concretes.clone();
            concrete.push((held_value_guard, old_value));
            let op = pg.o(Op::Assign(
                pin,
                Assignment {
                    dont_care,
                    concretes: concrete,
                },
            ));
            actions.push(Action::new(ctx.get_true(), op));

            // Local writes select the new saved state; otherwise hold it. X
            // releases the pin without sampling an arbitrary concrete value.
            let mut next_value = old_value;
            for &(guard, rhs) in local.concretes.iter().rev() {
                next_value = ctx.ite(guard, rhs, next_value);
            }
            next_value = ctx.ite(local.dont_care, old_value, next_value);
            // Every concrete write clears the release bit, irrespective of its
            // payload. Merge their guards before building the saved state.
            let next_x = ctx.ite(concrete_guard, ctx.get_false(), old_x);
            let next_x = ctx.ite(local.dont_care, ctx.get_true(), next_x);
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
