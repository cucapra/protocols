use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type};
use crate::ir::proto_graph::{Action, Assignment, Op, ProtoGraph};
use patronus::expr::{ExprRef, TypeCheck, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ToMonitorError {
    #[error("monitor parameters must be bit-vectors: {0}")]
    NonBitVectorParameter(String),
    #[error("assignment target has no expression in the ProtoGraph: {0:?}")]
    MissingAssignmentTarget(SymbolId),
    #[error("fork actions are only supported on the steady-state entry node")]
    UnsupportedFork,
}

#[derive(Clone, Copy)]
struct ParameterState {
    symbol: SymbolId,
    expr: ExprRef,
    known_symbol: SymbolId,
    known_expr: ExprRef,
}

fn expression_roots(pg: &ProtoGraph) -> Vec<ExprRef> {
    let mut roots = Vec::new();
    for (_, node) in pg.nodes() {
        for transition in &node.transitions {
            roots.push(transition.guard);
        }
        for action in &node.actions {
            roots.push(action.guard);
            match &pg[action.op] {
                Op::Assign(_, assignment) => {
                    roots.push(assignment.dont_care);
                    for (guard, rhs) in &assignment.concretes {
                        roots.push(*guard);
                        roots.push(*rhs);
                    }
                }
                Op::AssertEq(lhs, rhs) => {
                    roots.push(*lhs);
                    roots.push(*rhs);
                }
                Op::Fork | Op::InternalAssertFalse | Op::Done => {}
            }
        }
    }
    roots
}

fn referenced_symbols(pg: &mut ProtoGraph) -> FxHashMap<String, ExprRef> {
    let mut symbols = FxHashMap::default();
    for root in expression_roots(pg) {
        simple_transform_expr(&mut pg.expr_ctx, root, |ctx, candidate, _children| {
            if let Some(name) = ctx.get_symbol_name(candidate) {
                symbols.insert(name.to_string(), candidate);
            }
            None
        });
    }
    symbols
}

fn create_parameter_states(
    pg: &mut ProtoGraph,
    symbols: &mut SymbolTable,
) -> Result<Vec<ParameterState>, ToMonitorError> {
    let referenced = referenced_symbols(pg);
    let cached_args: Vec<(SymbolId, ExprRef)> = pg
        .symbol_expr
        .iter()
        .filter_map(|(symbol, expr)| {
            matches!(symbols[*symbol].kind(), SymbolKind::Arg(_)).then_some((*symbol, *expr))
        })
        .collect();

    // Steady-state lowering renames the one reusable argument bank with `#0`.
    // Multiple protocol scopes may contain the same argument name; those map to
    // the same monitor register, which is precisely the one-bank assumption.
    let mut by_expr: FxHashMap<ExprRef, SymbolId> = FxHashMap::default();
    for (symbol, cached_expr) in cached_args {
        let name = symbols.full_name_from_symbol_id(&symbol);
        let parameter_expr = referenced
            .get(&format!("{name}#0"))
            .or_else(|| referenced.get(&name))
            .copied()
            .unwrap_or(cached_expr);
        by_expr.entry(parameter_expr).or_insert(symbol);
    }

    let mut parameters = Vec::with_capacity(by_expr.len());
    for (expr, symbol) in by_expr {
        let width = expr.get_bv_type(&pg.expr_ctx).ok_or_else(|| {
            ToMonitorError::NonBitVectorParameter(symbols.full_name_from_symbol_id(&symbol))
        })?;
        let known_name = format!("__monitor_arg{}_known", symbol.as_u32());
        let known_symbol =
            if let Some(existing) = symbols.symbol_id_from_name_in_active_scope(&known_name) {
                existing
            } else {
                symbols.add_without_parent(
                    known_name.clone(),
                    Type::BitVec(1),
                    SymbolKind::MonitorState,
                )
            };
        let known_expr = pg.expr_ctx.bv_symbol(&known_name, 1);

        // Assigning the original argument SymbolId now updates its monitor
        // register. Cache the expression actually used by the steady-state PG.
        pg.cache_symbol_expr(symbol, expr);
        pg.cache_symbol_expr(known_symbol, known_expr);
        pg.state_init
            .insert(symbol, pg.expr_ctx.bit_vec_val(0, width));
        pg.state_init.insert(known_symbol, pg.false_id());
        parameters.push(ParameterState {
            symbol,
            expr,
            known_symbol,
            known_expr,
        });
    }
    Ok(parameters)
}

fn symbol_expr(
    pg: &mut ProtoGraph,
    symbols: &SymbolTable,
    symbol: SymbolId,
) -> Result<ExprRef, ToMonitorError> {
    if let Some(expr) = pg.symbol_expr(symbol) {
        return Ok(expr);
    }
    let Type::BitVec(width) = symbols[symbol].tpe() else {
        return Err(ToMonitorError::MissingAssignmentTarget(symbol));
    };
    let name = symbols.full_name_from_symbol_id(&symbol);
    let expr = pg.expr_ctx.bv_symbol(&name, width);
    pg.cache_symbol_expr(symbol, expr);
    Ok(expr)
}

fn parameters_in_expr(
    pg: &mut ProtoGraph,
    expr: ExprRef,
    by_expr: &FxHashMap<ExprRef, ParameterState>,
) -> Vec<ParameterState> {
    let mut found = FxHashSet::default();
    simple_transform_expr(&mut pg.expr_ctx, expr, |_ctx, candidate, _children| {
        if by_expr.contains_key(&candidate) {
            found.insert(candidate);
        }
        None
    });
    found
        .into_iter()
        .map(|candidate| by_expr[&candidate])
        .collect()
}

fn and_all(pg: &mut ProtoGraph, terms: impl IntoIterator<Item = ExprRef>) -> ExprRef {
    terms
        .into_iter()
        .fold(pg.true_id(), |acc, term| pg.and_guard(acc, term))
}

fn push_assign(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    guard: ExprRef,
    lhs: SymbolId,
    rhs: ExprRef,
) {
    let assignment = Assignment::concrete(pg.false_id(), pg.true_id(), rhs);
    let op = pg.o(Op::Assign(lhs, assignment));
    actions.push(Action::new(guard, op));
}

fn push_assert(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    guard: ExprRef,
    lhs: ExprRef,
    rhs: ExprRef,
) {
    let op = pg.o(Op::AssertEq(lhs, rhs));
    actions.push(Action::new(guard, op));
}

fn push_internal_assert_false(pg: &mut ProtoGraph, actions: &mut Vec<Action>, guard: ExprRef) {
    let op = pg.o(Op::InternalAssertFalse);
    actions.push(Action::new(guard, op));
}

/// Turn one equality into explicit learn/check actions.
///
/// A whole unknown parameter may be assigned from the other, fully-known side.
/// Once every referenced parameter is known, the equality is checked normally.
/// Any active case requiring partial or relational inference becomes an explicit
/// internal assertion failure in the monitor graph.
fn lower_equality(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    active: ExprRef,
    lhs: ExprRef,
    rhs: ExprRef,
    parameters: &FxHashMap<ExprRef, ParameterState>,
) {
    let lhs_parameters = parameters_in_expr(pg, lhs, parameters);
    let rhs_parameters = parameters_in_expr(pg, rhs, parameters);
    let mut all_parameters = lhs_parameters.clone();
    for parameter in &rhs_parameters {
        if !all_parameters
            .iter()
            .any(|other| other.expr == parameter.expr)
        {
            all_parameters.push(*parameter);
        }
    }

    if all_parameters.is_empty() {
        push_assert(pg, actions, active, lhs, rhs);
        return;
    }

    let all_known = and_all(
        pg,
        all_parameters.iter().map(|parameter| parameter.known_expr),
    );
    let check_guard = pg.and_guard(active, all_known);
    push_assert(pg, actions, check_guard, lhs, rhs);

    let mut handled = all_known;
    if let Some(parameter) = parameters.get(&lhs).copied() {
        let rhs_known = and_all(pg, rhs_parameters.iter().map(|other| other.known_expr));
        let lhs_unknown = pg.not_guard(parameter.known_expr);
        let can_bind = pg.and_guard(lhs_unknown, rhs_known);
        let bind_guard = pg.and_guard(active, can_bind);
        push_assign(pg, actions, bind_guard, parameter.symbol, rhs);
        push_assign(
            pg,
            actions,
            bind_guard,
            parameter.known_symbol,
            pg.true_id(),
        );
        handled = pg.or_guard(handled, can_bind);
    }
    if let Some(parameter) = parameters.get(&rhs).copied() {
        let lhs_known = and_all(pg, lhs_parameters.iter().map(|other| other.known_expr));
        let rhs_unknown = pg.not_guard(parameter.known_expr);
        let can_bind = pg.and_guard(rhs_unknown, lhs_known);
        let bind_guard = pg.and_guard(active, can_bind);
        push_assign(pg, actions, bind_guard, parameter.symbol, lhs);
        push_assign(
            pg,
            actions,
            bind_guard,
            parameter.known_symbol,
            pg.true_id(),
        );
        handled = pg.or_guard(handled, can_bind);
    }

    let unhandled = pg.not_guard(handled);
    let unsupported_guard = pg.and_guard(active, unhandled);
    push_internal_assert_false(pg, actions, unsupported_guard);
}

/// Convert a steady-state driver `ProtoGraph` into an explicit monitor graph.
///
/// DUT assignments become equalities against observed DUT ports. Whole unknown
/// arguments are learned with guarded `Op::Assign` actions; later observations
/// are checked with guarded `Op::AssertEq` actions. The one-bank assumption is
/// reflected by sharing a monitor register for each argument expression.
pub fn to_monitor(
    mut pg: ProtoGraph,
    symbols: &mut SymbolTable,
) -> Result<ProtoGraph, ToMonitorError> {
    let parameter_states = create_parameter_states(&mut pg, symbols)?;
    let parameters: FxHashMap<ExprRef, ParameterState> = parameter_states
        .iter()
        .map(|parameter| (parameter.expr, *parameter))
        .collect();
    let node_ids: Vec<_> = pg.nodes().map(|(node, _)| node).collect();

    for node_id in node_ids {
        let old_actions = pg[node_id].actions.clone();
        let transitions = pg[node_id].transitions.clone();
        let mut new_actions = Vec::new();

        for action in old_actions {
            match pg[action.op].clone() {
                Op::Assign(port, assignment) => {
                    let port_expr = symbol_expr(&mut pg, symbols, port)?;
                    for (assignment_guard, rhs) in assignment.concretes {
                        let active = pg.and_guard(action.guard, assignment_guard);
                        lower_equality(
                            &mut pg,
                            &mut new_actions,
                            active,
                            port_expr,
                            rhs,
                            &parameters,
                        );
                    }
                    // DontCare branches intentionally impose no monitor constraint.
                }
                Op::AssertEq(lhs, rhs) => lower_equality(
                    &mut pg,
                    &mut new_actions,
                    action.guard,
                    lhs,
                    rhs,
                    &parameters,
                ),
                Op::Fork if node_id == pg.entry => {}
                Op::Fork => return Err(ToMonitorError::UnsupportedFork),
                Op::InternalAssertFalse | Op::Done => new_actions.push(action),
            }
        }

        // A steady-state back-edge starts a fresh transaction. Clear all
        // knownness registers on the same edge that returns to the entry.
        let entry = pg.entry;
        let false_id = pg.false_id();
        for transition in transitions
            .iter()
            .filter(|transition| transition.target == entry)
        {
            for parameter in &parameter_states {
                push_assign(
                    &mut pg,
                    &mut new_actions,
                    transition.guard,
                    parameter.known_symbol,
                    false_id,
                );
            }
        }

        pg.node_mut(node_id).actions = new_actions;
    }

    pg.simplify_all_exprs();
    Ok(pg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::graphviz::to_dot_string;
    use crate::ir::steady_state_lowering::lower_steady_state;
    use patronus::expr::Context as ExprContext;
    use std::fs;
    use tempfile::NamedTempFile;

    fn lower_monitor(source: &str) -> (ProtoGraph, SymbolTable) {
        let file = NamedTempFile::new().unwrap();
        fs::write(file.path(), source).unwrap();
        let mut diagnostics = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[file.path()], &mut diagnostics, true).unwrap();
        let module = require_single_module(modules, &[file.path()]).unwrap();
        let (driver, _) = lower_steady_state(module.protos, &symbols, ExprContext::default());
        let monitor = to_monitor(driver, &mut symbols).unwrap();
        (monitor, symbols)
    }

    #[test]
    fn steady_state_driver_actions_become_explicit_monitor_state_updates() {
        let (monitor, symbols) = lower_monitor(
            r#"
            struct Device {
                in x: u32,
                out z: u32,
            }

            prot transaction<dut: Device>(a: u32) {
                dut.x := a;
                step();
                assert_eq(dut.z, a);
                step();
            }
            "#,
        );

        let mut saw_argument_update = false;
        let mut saw_knownness_update = false;
        let mut saw_monitor_assertion = false;

        for (_, node) in monitor.nodes() {
            for action in &node.actions {
                match &monitor[action.op] {
                    Op::Assign(symbol, _) => match symbols[*symbol].kind() {
                        SymbolKind::Arg(_) => saw_argument_update = true,
                        SymbolKind::MonitorState => saw_knownness_update = true,
                        SymbolKind::InPort | SymbolKind::OutPort => {
                            panic!("monitor graph still drives a DUT port")
                        }
                        SymbolKind::Dut | SymbolKind::LoopVar => {
                            panic!("unexpected monitor assignment target")
                        }
                    },
                    Op::AssertEq(_, _) => saw_monitor_assertion = true,
                    Op::Fork => panic!("synthetic steady-state fork was not removed"),
                    Op::InternalAssertFalse | Op::Done => {}
                }
            }
        }

        assert!(saw_argument_update);
        assert!(saw_knownness_update);
        assert!(saw_monitor_assertion);
        assert_eq!(
            monitor
                .state_init
                .keys()
                .filter(|symbol| symbols[**symbol].is_arg())
                .count(),
            1
        );
        assert_eq!(
            monitor
                .state_init
                .keys()
                .filter(|symbol| symbols[**symbol].is_monitor_state())
                .count(),
            1
        );
    }

    #[test]
    fn serializes_normal_swapped_monitor() {
        let (monitor, symbols) = lower_monitor(
            r#"
            struct Device {
                in x: u32,
                in y: u32,
                out z: u32,
            }

            prot normal<dut: Device>(a: u32, b: u32) {
                dut.x := a;
                dut.y := b;
                step();
                assert_eq(dut.z, a);
                step();
            }

            prot swapped<dut: Device>(a: u32, b: u32) {
                dut.x := b;
                dut.y := a;
                step();
                assert_eq(dut.z, a);
                step();
            }
            "#,
        );

        let serialized = to_dot_string(&monitor, &symbols);
        println!("{serialized}");
        assert!(serialized.contains("__monitor_arg"));
        assert!(serialized.contains("assert_eq"));
    }

    #[test]
    fn serializes_add_d0_monitor() {
        let (monitor, symbols) = lower_monitor(
            r#"
            struct Device {
                in a: u32,
                in b: u32,
                out s: u32,
            }

            prot add<dut: Device>(a: u32, b: u32, s: u32) {
                dut.a := a;
                dut.b := b;
                step();
                assert_eq(dut.s, s);
                step();
            }
            "#,
        );

        let serialized = to_dot_string(&monitor, &symbols);
        println!("{serialized}");
    }
}
