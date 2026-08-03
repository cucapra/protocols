use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type};
use crate::ir::determinize::{SatResult, check_sat, determinized};
use crate::ir::lowering::{LoweredFragmentInfo, Lowerer};
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use patronus::expr::{Context as ExprContext, ExprRef, simple_transform_expr};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ToMonitorError {
    #[error("cannot construct a monitor from an empty protocol set")]
    EmptyProtocolSet,
    #[error("monitor parameters must be bit-vectors: {0}")]
    NonBitVectorParameter(String),
    #[error("assignment target has no expression in the ProtoGraph: {0:?}")]
    MissingAssignmentTarget(SymbolId),
    #[error("monitor lowering does not support fork actions")]
    UnsupportedFork,
}

#[derive(Clone)]
struct ParameterSeed {
    original: SymbolId,
    symbol: SymbolId,
    known_symbol: SymbolId,
    name: String,
    known_name: String,
    width: u32,
}

#[derive(Clone)]
struct ProtocolSeed {
    live_symbol: SymbolId,
    live_name: String,
    parameters: Vec<ParameterSeed>,
}

struct CandidateState {
    live_symbol: SymbolId,
    live_expr: ExprRef,
    parameters: Vec<ParameterState>,
}

#[derive(Clone, Copy)]
struct ParameterState {
    symbol: SymbolId,
    expr: ExprRef,
    known_symbol: Option<SymbolId>,
    known_expr: Option<ExprRef>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Knownness {
    Unknown,
    Known,
    Maybe,
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

fn join_knownness(lhs: Knownness, rhs: Knownness) -> Knownness {
    if lhs == rhs { lhs } else { Knownness::Maybe }
}

fn or_all(pg: &mut ProtoGraph, guards: impl IntoIterator<Item = ExprRef>) -> ExprRef {
    guards
        .into_iter()
        .fold(pg.false_id(), |acc, guard| pg.or_guard(acc, guard))
}

fn node_equalities(pg: &mut ProtoGraph, node: NodeId) -> Vec<(ExprRef, ExprRef, ExprRef)> {
    let actions = pg[node].actions.clone();
    let mut equalities = Vec::new();
    for action in actions {
        match pg[action.op].clone() {
            Op::Assign(symbol, assignment) => {
                let lhs = pg.symbol_expr(symbol).unwrap();
                for (guard, rhs) in assignment.concretes {
                    let guard = pg.and_guard(action.guard, guard);
                    equalities.push((guard, lhs, rhs));
                }
            }
            Op::AssertEq(lhs, rhs) => equalities.push((action.guard, lhs, rhs)),
            Op::Fork | Op::InternalAssertFalse | Op::Done => {}
        }
    }
    equalities
}

fn transfer_knownness(
    pg: &mut ProtoGraph,
    node: NodeId,
    input: &FxHashMap<ExprRef, Knownness>,
    parameters: &FxHashMap<ExprRef, ParameterState>,
) -> FxHashMap<ExprRef, Knownness> {
    let equalities = node_equalities(pg, node);
    let mut output = input.clone();

    let mut definite: FxHashMap<ExprRef, Vec<ExprRef>> = FxHashMap::default();
    let mut possible: FxHashMap<ExprRef, Vec<ExprRef>> = FxHashMap::default();

    for (guard, lhs, rhs) in &equalities {
        for (candidate, other) in [(*lhs, *rhs), (*rhs, *lhs)] {
            if !parameters.contains_key(&candidate) {
                continue;
            }
            let dependencies = parameters_in_expr(pg, other, parameters);
            if dependencies
                .iter()
                .all(|dependency| input[&dependency.expr] == Knownness::Known)
            {
                definite.entry(candidate).or_default().push(*guard);
            }
            if dependencies
                .iter()
                .all(|dependency| input[&dependency.expr] != Knownness::Unknown)
            {
                possible.entry(candidate).or_default().push(*guard);
            }
        }
    }

    for parameter in parameters.values() {
        let definitely_learned = definite
            .remove(&parameter.expr)
            .map(|guards| or_all(pg, guards))
            .is_some_and(|guard| matches!(check_sat(pg, guard), SatResult::AlwaysSat));
        let possibly_learned = possible
            .remove(&parameter.expr)
            .map(|guards| or_all(pg, guards))
            .is_some_and(|guard| !matches!(check_sat(pg, guard), SatResult::DefinitelyUnsat));

        output.insert(
            parameter.expr,
            match (input[&parameter.expr], definitely_learned, possibly_learned) {
                (Knownness::Known, _, _) | (_, true, _) => Knownness::Known,
                (Knownness::Unknown, false, true) => Knownness::Maybe,
                (knownness, false, false) => knownness,
                (Knownness::Maybe, false, true) => Knownness::Maybe,
            },
        );
    }

    output
}

fn analyze_knownness(
    pg: &mut ProtoGraph,
    entry: NodeId,
    parameters: &FxHashMap<ExprRef, ParameterState>,
) -> FxHashMap<NodeId, FxHashMap<ExprRef, Knownness>> {
    let unknown: FxHashMap<ExprRef, Knownness> = parameters
        .keys()
        .map(|expr| (*expr, Knownness::Unknown))
        .collect();
    let mut input_facts = FxHashMap::default();
    input_facts.insert(entry, unknown.clone());
    let mut worklist = VecDeque::from([entry]);

    while let Some(node) = worklist.pop_front() {
        let output = transfer_knownness(pg, node, &input_facts[&node], parameters);
        let transitions = pg[node].transitions.clone();
        for transition in transitions {
            let incoming = output.clone();
            let changed = if let Some(existing) = input_facts.get_mut(&transition.target) {
                let old = existing.clone();
                for (expr, knownness) in incoming {
                    existing
                        .entry(expr)
                        .and_modify(|current| *current = join_knownness(*current, knownness))
                        .or_insert(knownness);
                }
                *existing != old
            } else {
                input_facts.insert(transition.target, incoming);
                true
            };
            if changed {
                worklist.push_back(transition.target);
            }
        }
    }

    input_facts
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
    let assignment = Assignment::concrete(pg.false_id(), guard, rhs);
    let op = pg.o(Op::Assign(lhs, assignment));
    actions.push(Action::new(pg.true_id(), op));
}

fn known_expr(
    pg: &ProtoGraph,
    parameter: ParameterState,
    facts: &FxHashMap<ExprRef, Knownness>,
) -> ExprRef {
    match facts[&parameter.expr] {
        Knownness::Unknown => pg.false_id(),
        Knownness::Known => pg.true_id(),
        Knownness::Maybe => parameter.known_expr.unwrap(),
    }
}

fn push_known_update(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    guard: ExprRef,
    parameter: ParameterState,
) {
    if let Some(symbol) = parameter.known_symbol {
        push_assign(pg, actions, guard, symbol, pg.true_id());
    }
}

fn push_candidate_failure(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    active: ExprRef,
    live_symbol: SymbolId,
    lhs: ExprRef,
    rhs: ExprRef,
) {
    let equal = pg.expr_ctx.equal(lhs, rhs);
    let mismatch = pg.not_guard(equal);
    let guard = pg.and_guard(active, mismatch);
    push_assign(pg, actions, guard, live_symbol, pg.false_id());
}

fn lower_candidate_equality(
    pg: &mut ProtoGraph,
    actions: &mut Vec<Action>,
    active: ExprRef,
    lhs: ExprRef,
    rhs: ExprRef,
    live_symbol: SymbolId,
    parameters: &FxHashMap<ExprRef, ParameterState>,
    facts: &FxHashMap<ExprRef, Knownness>,
) {
    if matches!(check_sat(pg, active), SatResult::DefinitelyUnsat) {
        return;
    }

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

    if all_parameters.is_empty()
        || all_parameters
            .iter()
            .all(|parameter| facts[&parameter.expr] == Knownness::Known)
    {
        push_candidate_failure(pg, actions, active, live_symbol, lhs, rhs);
        return;
    }

    if let Some(parameter) = parameters.get(&lhs).copied()
        && facts[&parameter.expr] == Knownness::Unknown
        && rhs_parameters
            .iter()
            .all(|other| facts[&other.expr] == Knownness::Known)
    {
        push_assign(pg, actions, active, parameter.symbol, rhs);
        push_known_update(pg, actions, active, parameter);
        return;
    }
    if let Some(parameter) = parameters.get(&rhs).copied()
        && facts[&parameter.expr] == Knownness::Unknown
        && lhs_parameters
            .iter()
            .all(|other| facts[&other.expr] == Knownness::Known)
    {
        push_assign(pg, actions, active, parameter.symbol, lhs);
        push_known_update(pg, actions, active, parameter);
        return;
    }

    let all_known = and_all(
        pg,
        all_parameters
            .iter()
            .map(|parameter| known_expr(pg, *parameter, facts))
            .collect::<Vec<_>>(),
    );
    let check_guard = pg.and_guard(active, all_known);
    push_candidate_failure(pg, actions, check_guard, live_symbol, lhs, rhs);

    let mut handled = all_known;
    if let Some(parameter) = parameters.get(&lhs).copied() {
        let rhs_known = and_all(
            pg,
            rhs_parameters
                .iter()
                .map(|other| known_expr(pg, *other, facts))
                .collect::<Vec<_>>(),
        );
        let lhs_unknown = pg.not_guard(known_expr(pg, parameter, facts));
        let can_bind = pg.and_guard(lhs_unknown, rhs_known);
        let bind_guard = pg.and_guard(active, can_bind);
        push_assign(pg, actions, bind_guard, parameter.symbol, rhs);
        push_known_update(pg, actions, bind_guard, parameter);
        handled = pg.or_guard(handled, can_bind);
    }
    if let Some(parameter) = parameters.get(&rhs).copied() {
        let lhs_known = and_all(
            pg,
            lhs_parameters
                .iter()
                .map(|other| known_expr(pg, *other, facts))
                .collect::<Vec<_>>(),
        );
        let rhs_unknown = pg.not_guard(known_expr(pg, parameter, facts));
        let can_bind = pg.and_guard(rhs_unknown, lhs_known);
        let bind_guard = pg.and_guard(active, can_bind);
        push_assign(pg, actions, bind_guard, parameter.symbol, lhs);
        push_known_update(pg, actions, bind_guard, parameter);
        handled = pg.or_guard(handled, can_bind);
    }

    let unsupported = pg.not_guard(handled);
    let unsupported = pg.and_guard(active, unsupported);
    push_assign(pg, actions, unsupported, live_symbol, pg.false_id());
}

fn learn_equality_knownness(
    pg: &mut ProtoGraph,
    active: ExprRef,
    lhs: ExprRef,
    rhs: ExprRef,
    parameters: &FxHashMap<ExprRef, ParameterState>,
    facts: &mut FxHashMap<ExprRef, Knownness>,
) {
    let active_sat = check_sat(pg, active);
    if matches!(active_sat, SatResult::DefinitelyUnsat) {
        return;
    }

    for (candidate, other) in [(lhs, rhs), (rhs, lhs)] {
        if !parameters.contains_key(&candidate) {
            continue;
        }
        let dependencies = parameters_in_expr(pg, other, parameters);
        if dependencies
            .iter()
            .all(|dependency| facts[&dependency.expr] == Knownness::Known)
        {
            let learned = if matches!(active_sat, SatResult::AlwaysSat) {
                Knownness::Known
            } else {
                Knownness::Maybe
            };
            facts.entry(candidate).and_modify(|knownness| {
                if *knownness == Knownness::Unknown {
                    *knownness = learned;
                }
            });
        }
    }
}

fn allocate_protocol_seeds(
    protos: &[Protocol],
    symbols: &mut SymbolTable,
) -> Result<Vec<ProtocolSeed>, ToMonitorError> {
    let mut seeds = Vec::with_capacity(protos.len());
    for protocol in protos {
        let prefix = protocol.name.clone();
        let live_name = format!("{prefix}_live");
        let live_symbol = symbols.add_without_parent(
            live_name.clone(),
            Type::BitVec(1),
            SymbolKind::MonitorState,
        );
        let mut parameters = Vec::with_capacity(protocol.args.len());
        for argument in &protocol.args {
            let original = argument.symbol();
            let Type::BitVec(width) = symbols[original].tpe() else {
                return Err(ToMonitorError::NonBitVectorParameter(
                    symbols.full_name_from_symbol_id(&original),
                ));
            };
            let argument_name = symbols[original].name();
            let name = format!("{prefix}_{argument_name}");
            let known_name = format!("{name}_known");
            let symbol = symbols.add_without_parent(
                name.clone(),
                Type::BitVec(width),
                SymbolKind::MonitorState,
            );
            let known_symbol = symbols.add_without_parent(
                known_name.clone(),
                Type::BitVec(1),
                SymbolKind::MonitorState,
            );
            parameters.push(ParameterSeed {
                original,
                symbol,
                known_symbol,
                name,
                known_name,
                width,
            });
        }
        seeds.push(ProtocolSeed {
            live_symbol,
            live_name,
            parameters,
        });
    }
    Ok(seeds)
}

fn instantiate_candidate(
    lowerer: &mut Lowerer<'_>,
    protocol: &Protocol,
    seed: &ProtocolSeed,
) -> (LoweredFragmentInfo, CandidateState) {
    let prototype = lowerer.lower_protocol_fragment(protocol, false, true);
    let mut substitutions = FxHashMap::default();
    let mut parameters = Vec::with_capacity(seed.parameters.len());

    for parameter in &seed.parameters {
        let expr = lowerer
            .ir
            .expr_ctx
            .bv_symbol(&parameter.name, parameter.width);
        lowerer.ir.cache_symbol_expr(parameter.symbol, expr);
        lowerer.ir.state_init.insert(
            parameter.symbol,
            lowerer.ir.expr_ctx.bit_vec_val(0, parameter.width),
        );
        if let Some(original_expr) = lowerer.ir.symbol_expr(parameter.original) {
            substitutions.insert(original_expr, expr);
        }
        parameters.push(ParameterState {
            symbol: parameter.symbol,
            expr,
            known_symbol: None,
            known_expr: None,
        });
    }

    let live_expr = lowerer.ir.expr_ctx.bv_symbol(&seed.live_name, 1);
    lowerer.ir.cache_symbol_expr(seed.live_symbol, live_expr);
    lowerer
        .ir
        .state_init
        .insert(seed.live_symbol, lowerer.ir.true_id());
    let fragment = lowerer.copy_protocol_fragment(prototype, &substitutions);
    (
        fragment,
        CandidateState {
            live_symbol: seed.live_symbol,
            live_expr,
            parameters,
        },
    )
}

fn transform_candidate_fragment(
    pg: &mut ProtoGraph,
    symbols: &SymbolTable,
    fragment: &LoweredFragmentInfo,
    seed: &ProtocolSeed,
    candidate: &mut CandidateState,
) -> Result<(), ToMonitorError> {
    for node_id in &fragment.nodes {
        for action in pg[*node_id].actions.clone() {
            if let Op::Assign(symbol, _) = pg[action.op] {
                symbol_expr(pg, symbols, symbol)?;
            }
        }
    }

    let mut parameters: FxHashMap<ExprRef, ParameterState> = candidate
        .parameters
        .iter()
        .map(|parameter| (parameter.expr, *parameter))
        .collect();
    let facts = analyze_knownness(pg, fragment.entry, &parameters);

    for (parameter, parameter_seed) in candidate.parameters.iter_mut().zip(&seed.parameters) {
        if !facts
            .values()
            .any(|fact| fact.get(&parameter.expr) == Some(&Knownness::Maybe))
        {
            continue;
        }
        let known_expr = pg.expr_ctx.bv_symbol(&parameter_seed.known_name, 1);
        pg.cache_symbol_expr(parameter_seed.known_symbol, known_expr);
        pg.state_init
            .insert(parameter_seed.known_symbol, pg.false_id());
        parameter.known_symbol = Some(parameter_seed.known_symbol);
        parameter.known_expr = Some(known_expr);
    }
    parameters = candidate
        .parameters
        .iter()
        .map(|parameter| (parameter.expr, *parameter))
        .collect();

    for node_id in facts.keys().copied().collect::<Vec<_>>() {
        let node_active = if node_id == fragment.entry {
            pg.true_id()
        } else {
            candidate.live_expr
        };
        let old_actions = pg[node_id].actions.clone();
        let mut actions = Vec::new();
        let mut local_facts = facts[&node_id].clone();
        for action in old_actions {
            match pg[action.op].clone() {
                Op::Assign(port, assignment) => {
                    let port_expr = symbol_expr(pg, symbols, port)?;
                    for (assignment_guard, rhs) in assignment.concretes {
                        let active = pg.and_guard(action.guard, assignment_guard);
                        let active = pg.and_guard(node_active, active);
                        lower_candidate_equality(
                            pg,
                            &mut actions,
                            active,
                            port_expr,
                            rhs,
                            candidate.live_symbol,
                            &parameters,
                            &local_facts,
                        );
                        learn_equality_knownness(
                            pg,
                            active,
                            port_expr,
                            rhs,
                            &parameters,
                            &mut local_facts,
                        );
                    }
                }
                Op::AssertEq(lhs, rhs) => {
                    let active = pg.and_guard(node_active, action.guard);
                    lower_candidate_equality(
                        pg,
                        &mut actions,
                        active,
                        lhs,
                        rhs,
                        candidate.live_symbol,
                        &parameters,
                        &local_facts,
                    );
                    learn_equality_knownness(pg, active, lhs, rhs, &parameters, &mut local_facts);
                }
                Op::Fork => return Err(ToMonitorError::UnsupportedFork),
                Op::InternalAssertFalse | Op::Done => {
                    let guard = pg.and_guard(node_active, action.guard);
                    actions.push(action.with_guard(guard));
                }
            }
        }

        let transitions = pg[node_id].transitions.clone();
        let transition_guards: Vec<_> = transitions
            .iter()
            .map(|transition| pg.expr_ctx.and(candidate.live_expr, transition.guard))
            .collect();
        pg.node_mut(node_id).actions = actions;
        for (transition, guard) in pg
            .node_mut(node_id)
            .transitions
            .iter_mut()
            .zip(transition_guards)
        {
            transition.guard = guard;
        }
    }
    initialize_candidate_entry(pg, fragment.entry, candidate);
    Ok(())
}

fn initialize_candidate_entry(pg: &mut ProtoGraph, entry: NodeId, candidate: &CandidateState) {
    let old_actions = pg[entry].actions.clone();
    let mut actions = Vec::new();
    let mut live_kills = Vec::new();
    let known_symbols: FxHashSet<_> = candidate
        .parameters
        .iter()
        .filter_map(|parameter| parameter.known_symbol)
        .collect();
    let mut known_sets: FxHashMap<SymbolId, Vec<ExprRef>> = FxHashMap::default();

    for action in old_actions {
        let Op::Assign(symbol, assignment) = pg[action.op].clone() else {
            actions.push(action);
            continue;
        };
        if symbol != candidate.live_symbol && !known_symbols.contains(&symbol) {
            actions.push(action);
            continue;
        }
        for (branch_guard, rhs) in assignment.concretes {
            let guard = pg.and_guard(action.guard, branch_guard);
            if symbol == candidate.live_symbol && rhs == pg.false_id() {
                live_kills.push(guard);
            } else if known_symbols.contains(&symbol) && rhs == pg.true_id() {
                known_sets.entry(symbol).or_default().push(guard);
            }
        }
    }

    let kill = or_all(pg, live_kills);
    let survives = pg.not_guard(kill);
    let live_assignment = Assignment {
        dont_care: pg.false_id(),
        concretes: vec![(kill, pg.false_id()), (survives, pg.true_id())],
    };
    let live_op = pg.o(Op::Assign(candidate.live_symbol, live_assignment));
    actions.push(Action::new(pg.true_id(), live_op));

    for parameter in &candidate.parameters {
        let Some(known_symbol) = parameter.known_symbol else {
            continue;
        };
        let set = or_all(pg, known_sets.remove(&known_symbol).unwrap_or_default());
        let clear = pg.not_guard(set);
        let assignment = Assignment {
            dont_care: pg.false_id(),
            concretes: vec![(set, pg.true_id()), (clear, pg.false_id())],
        };
        let op = pg.o(Op::Assign(known_symbol, assignment));
        actions.push(Action::new(pg.true_id(), op));
    }
    pg.node_mut(entry).actions = actions;
}

fn loop_fragment_exit_to_entry(
    pg: &mut ProtoGraph,
    fragment: &LoweredFragmentInfo,
    entry: NodeId,
    live_expr: ExprRef,
) {
    for node in fragment
        .nodes
        .iter()
        .copied()
        .filter(|node| *node != fragment.exit)
    {
        for transition in &mut pg.node_mut(node).transitions {
            if transition.target == fragment.exit {
                transition.target = entry;
                transition.consumes_step = true;
            }
        }
        let return_guards: Vec<_> = pg[node]
            .transitions
            .iter()
            .filter(|transition| transition.target == entry)
            .map(|transition| transition.guard)
            .collect();
        let return_guard = or_all(pg, return_guards);
        if return_guard != pg.false_id() {
            let done = pg.o(Op::Done);
            let done_guard = pg.and_guard(live_expr, return_guard);
            pg.push_action(node, Action::new(done_guard, done));
        }
    }
}

/// Lower protocols directly into a deterministic steady-state monitor.
///
/// Each protocol receives its own parameter bank and live bit. Observations
/// bind unknown parameters and eliminate only that protocol on a known-value
/// mismatch. The live protocol fragments are grafted together and subset
/// construction makes every surviving combination explicit.
pub fn to_monitor(
    protos: Vec<Protocol>,
    symbols: &mut SymbolTable,
    expr_ctx: ExprContext,
) -> Result<ProtoGraph, ToMonitorError> {
    let Some(first) = protos.first() else {
        return Err(ToMonitorError::EmptyProtocolSet);
    };
    let seeds = allocate_protocol_seeds(&protos, symbols)?;
    let mut lowerer = Lowerer::with_expr_ctx(first.ctx.clone(), symbols, expr_ctx);
    let mut fragments = Vec::with_capacity(protos.len());
    let mut candidates = Vec::with_capacity(protos.len());

    for (protocol, seed) in protos.iter().zip(&seeds) {
        let (fragment, candidate) = instantiate_candidate(&mut lowerer, protocol, seed);
        fragments.push(fragment);
        candidates.push(candidate);
    }

    for ((fragment, seed), candidate) in fragments.iter().zip(&seeds).zip(&mut candidates) {
        transform_candidate_fragment(&mut lowerer.ir, lowerer.symbols, fragment, seed, candidate)?;
    }

    let entry = lowerer.ir.entry;
    for (fragment, candidate) in fragments.iter().zip(&candidates) {
        loop_fragment_exit_to_entry(&mut lowerer.ir, fragment, entry, candidate.live_expr);
        lowerer.graft_contracted_entry(entry, fragment.entry, lowerer.ir.true_id());
    }

    lowerer.ir.simplify_all_exprs();
    let mut monitor = determinized(lowerer.ir, symbols);
    monitor.garbage_collect_unreachable();
    Ok(monitor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;
    use crate::frontend::require_single_module;
    use crate::ir::graphviz::to_dot_string;
    use patronus::expr::Context as ExprContext;
    use std::fs;
    use tempfile::NamedTempFile;

    fn lower_monitor(source: &str) -> (ProtoGraph, SymbolTable) {
        let file = NamedTempFile::new().unwrap();
        fs::write(file.path(), source).unwrap();
        let mut diagnostics = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[file.path()], &mut diagnostics, true).unwrap();
        let module = require_single_module(modules, &[file.path()]).unwrap();
        let monitor = to_monitor(module.protos, &mut symbols, ExprContext::default()).unwrap();
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

        assert!(!saw_argument_update);
        assert!(saw_knownness_update);
        assert!(!saw_monitor_assertion);
        assert_eq!(
            monitor
                .state_init
                .keys()
                .filter(|symbol| symbols[**symbol].is_arg())
                .count(),
            0
        );
        assert_eq!(
            monitor
                .state_init
                .keys()
                .filter(|symbol| symbols[**symbol].is_monitor_state())
                .count(),
            2
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
        println!("{}", serialized);
        assert!(!serialized.contains("proto_choice"));
        assert!(serialized.contains("_live"));
    }

    #[test]
    fn serializes_add_d0_monitor() {
        let (monitor, symbols) = lower_monitor(
            r#"
            struct Device {
                in a: u32,
                in b: u32,
                in op: u1,
                out s: u32,
            }

            prot add<dut: Device>(a: u32, b: u32, s: u32) {
                dut.a := a;
                dut.b := b;
                dut.op := 1'b0;
                step();
                dut.a := X;
                dut.b := X;
                assert_eq(dut.s, s);
                step();
            }

            prot sub<dut: Device>(a: u32, b: u32, s: u32) {
                dut.a := a;
                dut.b := b;
                dut.op := 1'b1;
                step();
                dut.a := X;
                dut.b := X;
                assert_eq(dut.s, s);
                step();
            }
            "#,
        );

        let serialized = to_dot_string(&monitor, &symbols);
        println!("{serialized}");
    }

    #[test]
    fn serializes_wishbone_read_write_monitor() {
        use crate::transaction_frontend;
        use std::collections::HashSet;

        let protocol_file = "../examples/wishbone/wishbone.prot";
        let trace_file = "../examples/wishbone/read_write.tx";
        let mut diagnostics = DiagnosticHandler::default();
        let (mut symbols, modules) = frontend(&[protocol_file], &mut diagnostics, true).unwrap();
        let module = require_single_module(modules, &[protocol_file]).unwrap();
        let traces =
            transaction_frontend(trace_file, &symbols, &module.protos, &mut diagnostics).unwrap();
        let selected_names: HashSet<_> = traces[0].iter().map(|(name, _)| name.as_str()).collect();
        let selected = module
            .protos
            .into_iter()
            .filter(|protocol| selected_names.contains(protocol.name.as_str()))
            .collect();

        let monitor = to_monitor(selected, &mut symbols, ExprContext::default()).unwrap();
        let serialized = to_dot_string(&monitor, &symbols);
        let output = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../scripts/wishbone_read_write_monitor.dot");
        fs::write(output, &serialized).unwrap();
        assert!(!serialized.contains("internal_assert_false"));
        println!("{serialized}");
    }
}
