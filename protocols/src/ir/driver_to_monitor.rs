use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, ForEachChild, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::symbol::{SymbolId, SymbolTable, Type};
use crate::ir::proto_graph::{
    Action, Assignment, LoopId, Node, NodeId, Op, ProtoGraph, remap_expr,
};
use crate::ir::register_simplify::simplify_registers;

#[derive(Clone)]
/// wrap an owned ProtoGraph in extra metadata (which is useful to simplify
/// and lower the MonitorAutomaton)
pub struct MonitorAutomaton {
    pub graph: ProtoGraph,
    /// Original argument -> register storing its value
    pub value_registers: FxHashMap<SymbolId, SymbolId>,
    /// Original argument -> registering storing which bits we know
    pub knownness_registers: FxHashMap<SymbolId, SymbolId>,
    /// Generated register -> its initial-value
    /// (For the naive monitor, value, and knownness registers all start 0,
    /// and the live register starts at 1, but as we optimize these can change).
    pub register_inits: FxHashMap<SymbolId, ExprRef>,
    /// the symbol that is true if a constraint hasn't failed yet.
    pub live_register: SymbolId,
}

impl MonitorAutomaton {
    pub fn to_dot_string(&self, ctx: &Context, symbols: &SymbolTable) -> String {
        crate::ir::graphviz::to_dot_string(ctx, &self.graph, symbols)
    }
}

/// Simplify register state and remove metadata for eliminated registers.
pub fn simplify_monitor(
    ctx: &mut Context,
    mut monitor: MonitorAutomaton,
    symbols: &mut SymbolTable,
) -> MonitorAutomaton {
    // Parameter values are captured results, even when no later check reads them.
    // Joint construction adds liveness reads after this simplification.
    let mut preserved = monitor
        .value_registers
        .values()
        .copied()
        .collect::<FxHashSet<_>>();
    preserved.insert(monitor.live_register);
    let entry = monitor.graph.entry;
    let dead = simplify_registers(
        ctx,
        &mut monitor.graph,
        symbols,
        entry,
        &monitor.register_inits,
        &preserved,
    );
    monitor.register_inits.retain(|r, _| !dead.contains(r));
    monitor.value_registers.retain(|_, r| !dead.contains(r));
    monitor.knownness_registers.retain(|_, r| !dead.contains(r));
    monitor.graph.register_inits = monitor.register_inits.clone();
    monitor.graph.garbage_collect_unreachable(ctx);
    monitor
}

#[derive(Debug, Error)]
pub enum MonitorConversionError {
    #[error(
        "unsupported monitor parameter {argument}: expected a bit vector or a sequence of bit vectors, got {tpe:?}"
    )]
    UnsupportedParameter { argument: String, tpe: Type },
    #[error("invalid prepared driver at {node}: {reason}")]
    InvalidPreparedGraph { node: NodeId, reason: String },
    #[error("unsupported monitor expression at {node}: {reason}")]
    UnsupportedExpression { node: NodeId, reason: String },
}

/// Precondition: ProtoGraph is a single-protocol graph after edge contraction,
/// assignment persistence lowering/register simplification, normalization, and cleanup.
/// Each node has one total effective assignment per DUT input, including held values and X releases.
/// Expressions must pass frontend well-formedness checks. At most one equality
/// operand may contain parameters; action, assignment, ITE, and edge conditions
/// must be parameter-free (including conditions introduced by contraction).
/// Sequence alternatives must be distinguishable on their first sample. FIFO
/// valid/last select specialized alternatives; their input constraints select
/// the monitor path. Remaining state is deterministic, as in the driver.
/// The returned graph is unoptimized.
pub fn convert_driver_to_monitor(
    ctx: &mut Context,
    graph: ProtoGraph,
    symbols: &mut SymbolTable,
) -> Result<MonitorAutomaton, MonitorConversionError> {
    convert_driver(ctx, graph, symbols, true)
}

/// Only converts assertions to monitor versions.
pub fn convert_driver_to_capturing_driver(
    ctx: &mut Context,
    graph: ProtoGraph,
    symbols: &mut SymbolTable,
) -> Result<MonitorAutomaton, MonitorConversionError> {
    convert_driver(ctx, graph, symbols, false)
}

fn convert_driver(
    ctx: &mut Context,
    mut graph: ProtoGraph,
    symbols: &mut SymbolTable,
    convert_assignments: bool,
) -> Result<MonitorAutomaton, MonitorConversionError> {
    if !convert_assignments && !graph.loops.is_empty() {
        return Err(MonitorConversionError::UnsupportedExpression {
            node: graph.entry,
            reason: "capturing drivers with iterator loops are not supported yet".into(),
        });
    }
    // Sequence lengths are not items to capture.
    // Retain a bound as an ordinary parameter only if the body also reads it.
    let length_parameters = graph
        .loops
        .values()
        .filter_map(|source| source.source.length)
        .collect::<FxHashSet<_>>();
    let mut reads = FxHashSet::default();
    if !length_parameters.is_empty() {
        for (_, node) in graph.nodes() {
            let mut expressions = node.transitions.iter().map(|t| t.guard).collect::<Vec<_>>();
            for action in &node.actions {
                expressions.push(action.guard);
                match &graph[action.op] {
                    Op::Assign(_, assignment) => {
                        expressions.push(assignment.dont_care);
                        expressions.extend(assignment.concretes.iter().flat_map(|&(g, v)| [g, v]));
                    }
                    Op::AssertEq(a, b) => expressions.extend([*a, *b]),
                    _ => {}
                }
            }
            for expression in expressions {
                reads.extend(patronus::expr::find_symbols(ctx, expression));
            }
        }
    }
    let arguments = graph
        .args
        .iter()
        .filter(|arg| {
            graph
                .symbol_expr(arg.symbol())
                .is_none_or(|expr| !length_parameters.contains(&expr) || reads.contains(&expr))
        })
        .cloned()
        .collect::<Vec<_>>();
    graph.args = arguments.clone();
    let mut value_registers = FxHashMap::default();
    let mut knownness_registers = FxHashMap::default();
    let mut register_inits = graph.register_inits.clone();
    let mut parameter_exprs = FxHashMap::default();
    let mut items = FxHashMap::default();

    let mut captures = 0;
    for (id, source) in graph.loops.clone().iter() {
        let fixed_length = source.source.length.and_then(|length| {
            if let Expr::BVLiteral(value) = ctx[length] {
                Some(value.get(ctx).to_u64().unwrap())
            } else {
                None
            }
        });
        let minimum = fixed_length.unwrap_or(source.source.min_len);
        let exact = fixed_length.is_some();
        // Count only the items still required by the declared minimum. The
        // counter saturates at zero, so arbitrarily long sequences stay legal.
        let remaining = (minimum != 0 || exact).then(|| {
            let width = (u64::BITS - minimum.leading_zeros()).max(1);
            let register =
                graph.add_register(ctx, symbols, &format!("$monitor_{id}_remaining"), width);
            register_inits.insert(register, ctx.bit_vec_val(minimum, width));
            register
        });
        let capture = source.source.argument.map(|argument| {
            let saved = arguments
                .iter()
                .position(|a| a.symbol() == argument)
                .unwrap();
            let fresh = arguments.len() + captures;
            captures += 1;
            parameter_exprs.insert(source.data, fresh);
            (saved, fresh)
        });
        items.insert(
            id,
            ItemBinding {
                capture,
                remaining,
                exact,
            },
        );
    }
    for op in graph
        .nodes()
        .flat_map(|(_, node)| node.actions.iter())
        .map(|a| &graph[a.op])
    {
        match *op {
            Op::Data { loop_id, target } => {
                let (saved, _) = items[&loop_id].capture.unwrap();
                parameter_exprs.insert(graph.symbol_expr(target).unwrap(), saved);
                register_inits.remove(&target);
            }
            Op::Valid { target, .. } => {
                register_inits.remove(&target);
            }
            _ => {}
        }
    }

    // create value and knownness registers for every parameter,
    // and initialize both to zero
    for (index, arg) in arguments.iter().enumerate() {
        let argument = arg.symbol();
        let tpe = symbols[argument].tpe();
        let width = match tpe {
            Type::BitVec(width) if width > 0 => width,
            Type::Seq(seq) if matches!(symbols[seq].tpe(), Type::BitVec(_)) => {
                symbols[seq].tpe().bitwidth()
            }
            tpe => {
                return Err(MonitorConversionError::UnsupportedParameter {
                    argument: symbols[argument].full_name(symbols),
                    tpe,
                });
            }
        };
        if matches!(tpe, Type::BitVec(_)) {
            let expr = symbol_expr(ctx, &mut graph, symbols, argument);
            parameter_exprs.insert(expr, index);
        }
        let name = symbols[argument].name().to_string();
        let value = graph.add_register(ctx, symbols, &format!("$monitor_{name}_value"), width);
        let known = graph.add_register(ctx, symbols, &format!("$monitor_{name}_known"), width);
        value_registers.insert(argument, value);
        knownness_registers.insert(argument, known);
        let zero = ctx.zero(width);
        register_inits.extend([(value, zero), (known, zero)]);
    }

    // allocate liveness register, set it to 1.
    let live_register = graph.add_register(ctx, symbols, "$monitor_live", 1);
    register_inits.insert(live_register, ctx.get_true());

    // Cache pin expressions, including pins used only as assignment targets.
    let pins: Vec<_> = graph.dut_pins(symbols).collect();
    let mut sampled_x = FxHashMap::default();
    for pin in pins {
        let sample = symbol_expr(ctx, &mut graph, symbols, pin);
        let alias = ctx.bv_symbol(
            &format!("dont_care.{}", symbols[pin].name()),
            symbols[pin].tpe().bitwidth(),
        );
        if graph.dont_cares.remove(&alias) {
            sampled_x.insert(alias, sample);
        }
    }
    // An X drive is unconstrained, but a later read of that pin is still a
    // concrete waveform observation. Contraction used an independent X input
    // so an earlier write could not replace that read while composing nodes.
    for (_, op) in graph.ops_mut() {
        *op = op.remap(ctx, &sampled_x, &FxHashMap::default());
    }
    for (_, node) in graph.nodes_mut() {
        for action in &mut node.actions {
            action.guard = remap_expr(ctx, action.guard, &sampled_x);
        }
        for edge in &mut node.transitions {
            edge.guard = remap_expr(ctx, edge.guard, &sampled_x);
        }
    }
    let initial_env: Vec<Binding> = arguments
        .iter()
        .map(|arg| Binding {
            value: graph.symbol_expr(value_registers[&arg.symbol()]).unwrap(),
            known: graph
                .symbol_expr(knownness_registers[&arg.symbol()])
                .unwrap(),
        })
        .collect();

    let nodes = graph.reachable_node_ids(ctx, graph.entry);
    let input_pins = graph.proto_ctx.dut_input_symbols(symbols).collect();
    let mut converter = Converter {
        ctx,
        graph: &mut graph,
        value_registers: &value_registers,
        knownness_registers: &knownness_registers,
        parameter_exprs,
        parameter_dependencies: FxHashMap::default(),
        convert_assignments,
        items,
        input_pins,
    };

    for node in nodes {
        converter.convert_alternatives(node, &initial_env)?;
    }
    graph.loops.clear();
    graph.register_inits = register_inits.clone();
    // Drop obsolete driver operations, without optimizing monitor expressions.
    graph.garbage_collect_unreachable(ctx);
    Ok(MonitorAutomaton {
        graph,
        value_registers,
        knownness_registers,
        register_inits,
        live_register,
    })
}

/// wrap the ProtoGraph `symbol_expr` method with an extra
/// method that allows us to create an `expr` for the symbol,
/// if it doesn't already exist.
fn symbol_expr(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &SymbolTable,
    symbol: SymbolId,
) -> ExprRef {
    if let Some(expr) = graph.symbol_expr(symbol) {
        return expr;
    }
    let expr = ctx.bv_symbol(
        &symbols[symbol].full_name(symbols),
        symbols[symbol].tpe().bitwidth(),
    );
    graph.cache_symbol_expr(symbol, expr);
    expr
}

#[derive(Clone, Copy)]
struct Binding {
    value: ExprRef,
    known: ExprRef,
}

#[derive(Clone, Copy)]
struct ItemBinding {
    capture: Option<(usize, usize)>,
    remaining: Option<SymbolId>,
    exact: bool,
}

struct Converter<'a> {
    ctx: &'a mut Context,
    graph: &'a mut ProtoGraph,
    value_registers: &'a FxHashMap<SymbolId, SymbolId>,
    knownness_registers: &'a FxHashMap<SymbolId, SymbolId>,
    parameter_exprs: FxHashMap<ExprRef, usize>,
    parameter_dependencies: FxHashMap<ExprRef, bool>,
    convert_assignments: bool,
    items: FxHashMap<LoopId, ItemBinding>,
    input_pins: FxHashSet<SymbolId>,
}

impl Converter<'_> {
    fn substitute(&mut self, expr: ExprRef, values: &FxHashMap<ExprRef, ExprRef>) -> ExprRef {
        let expr = remap_expr(self.ctx, expr, values);
        self.graph.simplifier.simplify(self.ctx, expr)
    }

    fn specialize(&mut self, mut node: Node, values: &FxHashMap<ExprRef, ExprRef>) -> Node {
        for action in &mut node.actions {
            action.guard = self.substitute(action.guard, values);
            let mut op = self.graph[action.op].clone();
            match &mut op {
                Op::Assign(_, a) => {
                    a.dont_care = self.substitute(a.dont_care, values);
                    for (guard, rhs) in &mut a.concretes {
                        *guard = self.substitute(*guard, values);
                        *rhs = self.substitute(*rhs, values);
                    }
                    a.concretes.retain(|(g, _)| *g != self.ctx.get_false());
                }
                Op::AssertEq(a, b) => {
                    *a = self.substitute(*a, values);
                    *b = self.substitute(*b, values);
                }
                _ => {}
            }
            action.op = self.graph.o(op);
        }
        for edge in &mut node.transitions {
            edge.guard = self.substitute(edge.guard, values);
        }
        node.actions.retain(|a| a.guard != self.ctx.get_false());
        node.transitions.retain(|e| e.guard != self.ctx.get_false());
        node
    }

    // Alternatives are resolved from this sample. They share incoming state,
    // but only the matching alternative commits its captures and state updates.
    fn convert_alternatives(
        &mut self,
        node: NodeId,
        initial_env: &[Binding],
    ) -> Result<(), MonitorConversionError> {
        let original = self.graph[node].clone();
        let mut variants = vec![(original.clone(), self.ctx.get_true())];
        let mut heads = FxHashSet::default();
        for action in &original.actions {
            if let Op::Valid { loop_id, .. } = self.graph[action.op] {
                heads.insert(loop_id);
            }
        }
        if heads.is_empty() {
            return self.convert_node(node, initial_env);
        }
        let mut heads = heads.into_iter().collect::<Vec<_>>();
        heads.sort();
        for id in heads {
            let fifo = self.graph.loops[id].clone();
            let item = self.items[&id];
            let mut expressions = original
                .transitions
                .iter()
                .map(|t| t.guard)
                .collect::<Vec<_>>();
            for a in &original.actions {
                expressions.push(a.guard);
                if let Op::Assign(_, assign) = &self.graph[a.op] {
                    expressions.push(assign.dont_care);
                    expressions.extend(assign.concretes.iter().flat_map(|&(g, v)| [g, v]));
                }
            }
            let uses_last = expressions
                .into_iter()
                .any(|e| patronus::expr::find_symbols(self.ctx, e).contains(&fifo.last));
            let choices = if uses_last {
                &[(false, false), (true, false), (true, true)][..]
            } else {
                &[(false, false), (true, false)][..]
            };
            let mut next = Vec::new();
            for (body, allowed) in variants {
                // An earlier empty loop can expose another head in this
                // sample. Its guard already includes those earlier choices.
                let mut head = self.ctx.get_false();
                for action in &body.actions {
                    if matches!(self.graph[action.op], Op::Valid { loop_id, .. } if loop_id == id) {
                        head = self.graph.or_guard(self.ctx, head, action.guard);
                    }
                }
                for &(valid, last) in choices {
                    let bit = |b| {
                        if b {
                            self.ctx.get_true()
                        } else {
                            self.ctx.get_false()
                        }
                    };
                    let values =
                        FxHashMap::from_iter([(fifo.valid, bit(valid)), (fifo.last, bit(last))]);
                    let mut body = self.specialize(body.clone(), &values);
                    let mut allowed = allowed;
                    if let Some(register) = item.remaining {
                        let remaining = self.graph.symbol_expr(register).unwrap();
                        let width = remaining.get_bv_type(self.ctx).unwrap();
                        let zero = self.ctx.zero(width);
                        let one = self.ctx.bit_vec_val(1, width);
                        let empty = self.ctx.equal(remaining, zero);
                        let mut head_values = values.clone();
                        head_values.insert(fifo.valid, self.ctx.get_true());
                        let evaluated = self.substitute(head, &head_values);
                        if item.exact || !valid || last {
                            let enough = if !valid {
                                empty
                            } else if item.exact {
                                if last {
                                    self.ctx.equal(remaining, one)
                                } else if uses_last {
                                    self.ctx.greater(remaining, one)
                                } else {
                                    self.ctx.greater(remaining, zero)
                                }
                            } else {
                                self.ctx.greater_or_equal(one, remaining)
                            };
                            let not_evaluated = self.graph.not_guard(self.ctx, evaluated);
                            let enough = self.graph.or_guard(self.ctx, not_evaluated, enough);
                            allowed = self.graph.and_guard(self.ctx, allowed, enough);
                        }
                        if valid {
                            let decremented = self.ctx.sub(remaining, one);
                            let next = self.ctx.ite(empty, zero, decremented);
                            let op = self.graph.o(Op::Assign(
                                register,
                                Assignment::concrete(self.ctx.get_false(), evaluated, next),
                            ));
                            body.actions.push(Action::new(self.ctx.get_true(), op));
                        }
                    }
                    next.push((body, allowed));
                }
            }
            variants = next;
        }
        let mut merged = Node::empty();
        let mut updates: FxHashMap<SymbolId, Assignment> = FxHashMap::default();
        let mut survives = self.ctx.get_false();
        for (body, mut matches) in variants {
            *self.graph.node_mut(node) = body;
            self.convert_node(node, initial_env)?;
            let body = self.graph[node].clone();
            for action in &body.actions {
                let failed = match self.graph[action.op] {
                    Op::AssertEq(a, b) => {
                        let equal = self.ctx.equal(a, b);
                        self.graph.not_guard(self.ctx, equal)
                    }
                    Op::InternalAssertFalse => self.ctx.get_true(),
                    _ => continue,
                };
                let failed = self.graph.and_guard(self.ctx, action.guard, failed);
                let passes = self.graph.not_guard(self.ctx, failed);
                matches = self.graph.and_guard(self.ctx, matches, passes);
            }
            if matches == self.ctx.get_false() {
                continue;
            }
            survives = self.graph.or_guard(self.ctx, survives, matches);
            for action in body.actions {
                match self.graph[action.op].clone() {
                    Op::Assign(target, assignment) => {
                        let update = updates.entry(target).or_insert_with(|| Assignment {
                            dont_care: self.ctx.get_false(),
                            concretes: Vec::new(),
                        });
                        let selected = self.graph.and_guard(self.ctx, matches, action.guard);
                        for (guard, rhs) in assignment.concretes {
                            let guard = self.graph.and_guard(self.ctx, selected, guard);
                            update.concretes.push((guard, rhs));
                        }
                    }
                    Op::AssertEq(..) | Op::InternalAssertFalse => {}
                    _ => merged.actions.push(action.with_guard(self.graph.and_guard(
                        self.ctx,
                        matches,
                        action.guard,
                    ))),
                }
            }
            for edge in body.transitions {
                let guard = self.graph.and_guard(self.ctx, matches, edge.guard);
                if guard != self.ctx.get_false() {
                    if let Some(existing) = merged.transitions.iter_mut().find(|e| {
                        e.target == edge.target
                            && e.consumes_step == edge.consumes_step
                            && e.rotations == edge.rotations
                    }) {
                        existing.guard = self.graph.or_guard(self.ctx, existing.guard, guard);
                    } else {
                        merged.transitions.push(edge.with_guard(guard));
                    }
                }
            }
        }
        let mut updates = updates.into_iter().collect::<Vec<_>>();
        updates.sort_by_key(|(r, _)| *r);
        for (register, assignment) in updates {
            self.emit(
                &mut merged.actions,
                self.ctx.get_true(),
                Op::Assign(register, assignment),
            );
        }
        self.emit(
            &mut merged.actions,
            self.ctx.get_true(),
            Op::AssertEq(survives, self.ctx.get_true()),
        );
        *self.graph.node_mut(node) = merged;
        Ok(())
    }

    fn unsupported(&self, node: NodeId, reason: impl Into<String>) -> MonitorConversionError {
        MonitorConversionError::UnsupportedExpression {
            node,
            reason: reason.into(),
        }
    }

    // Check if an expression uses a parameter (with a cache to save on repeated work)
    fn contains_parameter(&mut self, expr: ExprRef) -> bool {
        if let Some(&contains) = self.parameter_dependencies.get(&expr) {
            return contains;
        }
        let mut contains = self.parameter_exprs.contains_key(&expr);
        if !contains {
            let mut children = Vec::new();
            self.ctx[expr].for_each_child(|child| children.push(*child));
            contains = children
                .into_iter()
                .any(|child| self.contains_parameter(child));
        }
        self.parameter_dependencies.insert(expr, contains);
        contains
    }

    fn emit(&mut self, actions: &mut Vec<Action>, guard: ExprRef, op: Op) {
        let op = self.graph.o(op);
        actions.push(Action::new(guard, op));
    }

    fn check_condition(
        &mut self,
        node: NodeId,
        condition: ExprRef,
    ) -> Result<(), MonitorConversionError> {
        if self.contains_parameter(condition) {
            return Err(self.unsupported(node, "parameter-dependent conditions are unsupported"));
        }
        Ok(())
    }

    /// switches a node from a driver version toa  monitor version
    fn convert_node(
        &mut self,
        node: NodeId,
        initial_env: &[Binding],
    ) -> Result<(), MonitorConversionError> {
        // helper closure to concisely generate errors.
        let invalid =
            |reason: String| MonitorConversionError::InvalidPreparedGraph { node, reason };

        let mut env = initial_env.to_vec();
        let mut items = self
            .items
            .values()
            .filter_map(|item| item.capture)
            .collect::<Vec<_>>();
        items.sort_by_key(|&(_, fresh)| fresh);
        for &(saved, _) in &items {
            let width = env[saved].value.get_bv_type(self.ctx).unwrap();
            let zero = self.ctx.zero(width);
            env.push(Binding {
                value: zero,
                known: zero,
            });
        }
        let mut actions = Vec::new();
        let mut updates = Vec::new();
        let mut checks = Vec::new();
        let mut loads = FxHashMap::default();
        // Defer arithmetic assertions until after pin observations: interface
        // mappings can assert omitted sum bits whose carry needs captured bits.
        // Keep other observations in order so constant captures stay simple.
        for action in self.graph[node].actions.clone() {
            self.check_condition(node, action.guard)?;
            match self.graph[action.op].clone() {
                Op::Data { .. } => {}
                Op::Valid { loop_id, .. } => {
                    if let Some((saved, _)) = self.items[&loop_id].capture {
                        loads.insert(saved, action.guard);
                    }
                }
                Op::Last { .. } => {
                    return Err(self.unsupported(
                        node,
                        "stored last flags must be specialized before monitor conversion",
                    ));
                }
                // Capturing drivers still drive their inputs normally.
                op @ Op::Assign(..) if !self.convert_assignments => {
                    self.emit(&mut actions, action.guard, op);
                }
                Op::Assign(register, _) if !self.input_pins.contains(&register) => {
                    updates.push(action);
                }
                // Assignment conversion. Here is an example:
                // dont_care = x
                // concretes = [(g1, p), (g2, q)]
                //
                // becomes:
                //
                // [!x && g1]        observe DUT.pin == p
                // [!x && !g1 && g2] observe DUT.pin == q
                Op::Assign(pin, assignment) => {
                    if action.guard != self.ctx.get_true() {
                        return Err(invalid("assignment action guards must be true".into()));
                    }
                    self.check_condition(node, assignment.dont_care)?;
                    let sample = self.graph.symbol_expr(pin).unwrap();
                    // X wins, then the first applicable concrete alternative.
                    let mut prior = assignment.dont_care;
                    for (guard, rhs) in assignment.concretes {
                        self.check_condition(node, guard)?;
                        let not_prior = self.graph.not_guard(self.ctx, prior);
                        let effective = self.graph.and_guard(self.ctx, not_prior, guard);
                        self.observe_equality(
                            node,
                            effective,
                            sample,
                            rhs,
                            &mut env,
                            &mut actions,
                        )?;
                        prior = self.graph.or_guard(self.ctx, prior, guard);
                    }
                }
                Op::AssertEq(lhs, rhs)
                    if self.contains_addition(lhs) || self.contains_addition(rhs) =>
                {
                    checks.push((action.guard, lhs, rhs));
                }
                Op::AssertEq(lhs, rhs) => {
                    self.observe_equality(node, action.guard, lhs, rhs, &mut env, &mut actions)?;
                }
                // retain all other ops as is.
                op @ (Op::Fork | Op::Done | Op::InternalAssertFalse) => {
                    self.emit(&mut actions, action.guard, op);
                }
            }
        }
        for (guard, lhs, rhs) in checks {
            self.observe_equality(node, guard, lhs, rhs, &mut env, &mut actions)?;
        }
        for edge in self.graph[node].transitions.clone() {
            self.check_condition(node, edge.guard)?;
        }
        // State writes are non-blocking. Their RHSs use the incoming item or
        // the freshly learned item according to the original expression.
        let values = self
            .parameter_exprs
            .iter()
            .map(|(&expr, &i)| (expr, env[i].value))
            .collect();
        for mut action in updates {
            action.op =
                self.graph
                    .o(self.graph[action.op].remap(self.ctx, &values, &FxHashMap::default()));
            actions.push(action);
        }
        let mut next = env[..initial_env.len()].to_vec();
        for (saved, fresh) in items {
            if let Some(&guard) = loads.get(&saved) {
                next[saved] = Binding {
                    value: self.ctx.ite(guard, env[fresh].value, env[saved].value),
                    known: self.ctx.ite(guard, env[fresh].known, env[saved].known),
                };
            }
        }
        for (index, binding) in next.into_iter().enumerate() {
            let argument = self.graph.args[index].symbol();
            for (register, rhs) in [
                (self.value_registers[&argument], binding.value),
                (self.knownness_registers[&argument], binding.known),
            ] {
                let assignment =
                    Assignment::concrete(self.ctx.get_false(), self.ctx.get_true(), rhs);
                self.emit(
                    &mut actions,
                    self.ctx.get_true(),
                    Op::Assign(register, assignment),
                );
            }
        }
        self.graph.node_mut(node).actions = actions;
        Ok(())
    }

    fn observe_equality(
        &mut self,
        node: NodeId,
        guard: ExprRef,
        lhs: ExprRef,
        rhs: ExprRef,
        env: &mut Vec<Binding>,
        actions: &mut Vec<Action>,
    ) -> Result<(), MonitorConversionError> {
        if guard == self.ctx.get_false() {
            return Ok(());
        }
        // An effective whole-value X is a release, with no observation.
        if self.graph.dont_cares.contains(&lhs) || self.graph.dont_cares.contains(&rhs) {
            return Ok(());
        }
        let left_has_parameter = self.contains_parameter(lhs);
        let right_has_parameter = self.contains_parameter(rhs);
        if left_has_parameter && right_has_parameter {
            return Err(self.unsupported(
                node,
                "equalities with parameters on both sides are unsupported",
            ));
        }
        let (sample, pattern) = if left_has_parameter {
            (rhs, lhs)
        } else {
            (lhs, rhs)
        };
        let width = pattern.get_bv_type(self.ctx).unwrap();
        if sample.get_bv_type(self.ctx) != Some(width) {
            return Err(self.unsupported(node, "equality operands must have the same bit width"));
        }
        if !left_has_parameter && !right_has_parameter {
            self.emit(actions, guard, Op::AssertEq(lhs, rhs));
            return Ok(());
        }
        self.observe_range(node, guard, sample, pattern, (width - 1, 0), env, actions)
    }

    /// This is the "workhorse" method for driver to monitor conversion,
    /// which solves for the parameter to generate an equality constriant.
    #[allow(clippy::too_many_arguments)]
    fn observe_range(
        &mut self,
        node: NodeId,
        guard: ExprRef,
        sample: ExprRef,
        pattern: ExprRef,
        (hi, lo): (u32, u32),
        env: &mut Vec<Binding>,
        actions: &mut Vec<Action>,
    ) -> Result<(), MonitorConversionError> {
        if guard == self.ctx.get_false() {
            return Ok(());
        }
        // X leaf: these bits impose no constraint.
        if self.graph.dont_cares.contains(&pattern) {
            return Ok(());
        }
        // Parameter leaf: check and learn its bits hi:lo from the sample.
        if let Some(&parameter) = self.parameter_exprs.get(&pattern) {
            self.learn(guard, sample, parameter, (hi, lo), env, actions);
            return Ok(());
        }
        // Otherwise recurse through the expression, or check parameter-free bits directly
        match self.ctx[pattern].clone() {
            Expr::BVAdd(a, b, _) => {
                let (unknown, offset) =
                    match (self.contains_parameter(a), self.contains_parameter(b)) {
                        (true, false) => (a, b),
                        (false, true) => (b, a),
                        (false, false) => {
                            let expected = self.ctx.slice(pattern, hi, lo);
                            self.emit(actions, guard, Op::AssertEq(sample, expected));
                            return Ok(());
                        }
                        _ => {
                            return Err(self.unsupported(
                                node,
                                "addition must have only one parameter-dependent operand",
                            ));
                        }
                    };
                let mut offset_part = self.ctx.slice(offset, hi, lo);
                if lo != 0 {
                    let low_offset = self.ctx.slice(offset, lo - 1, 0);
                    let low_offset = self.graph.simplifier.simplify(self.ctx, low_offset);
                    if low_offset != self.ctx.zero(lo) {
                        // The omitted low bits can carry into the observed
                        // slice. Use already captured bits; never assume zero.
                        let low_unknown = self
                            .captured_range(unknown, (lo - 1, 0), env)
                            .ok_or_else(|| {
                                self.unsupported(node,
                                "sliced addition has an unresolved carry from unobserved low bits")
                            })?;
                        let low_unknown = self.ctx.zero_extend(low_unknown, 1);
                        let low_offset = self.ctx.zero_extend(low_offset, 1);
                        let sum = self.ctx.add(low_unknown, low_offset);
                        let carry = self.ctx.slice(sum, lo, lo);
                        let carry = self.ctx.zero_extend(carry, hi - lo);
                        offset_part = self.ctx.add(offset_part, carry);
                    }
                }
                let observed = self.ctx.sub(sample, offset_part);
                self.observe_range(node, guard, observed, unknown, (hi, lo), env, actions)?;
            }
            Expr::BVSlice { e, lo: offset, .. } => {
                self.observe_range(
                    node,
                    guard,
                    sample,
                    e,
                    (hi + offset, lo + offset),
                    env,
                    actions,
                )?;
            }
            Expr::BVConcat(left, right, _) => {
                let right_width = right.get_bv_type(self.ctx).unwrap();
                if hi >= right_width {
                    let start = lo.max(right_width);
                    let part = self.ctx.slice(sample, hi - lo, start - lo);
                    self.observe_range(
                        node,
                        guard,
                        part,
                        left,
                        (hi - right_width, start - right_width),
                        env,
                        actions,
                    )?;
                }
                if lo < right_width {
                    let end = hi.min(right_width - 1);
                    let part = self.ctx.slice(sample, end - lo, 0);
                    self.observe_range(node, guard, part, right, (end, lo), env, actions)?;
                }
            }
            Expr::BVIte { cond, tru, fals } => {
                self.check_condition(node, cond)?;
                let true_guard = self.graph.and_guard(self.ctx, guard, cond);
                let not_cond = self.graph.not_guard(self.ctx, cond);
                let false_guard = self.graph.and_guard(self.ctx, guard, not_cond);
                // Both branches start from the same incoming expressions.
                let mut true_env = env.clone();
                let mut false_env = env.clone();
                self.observe_range(
                    node,
                    true_guard,
                    sample,
                    tru,
                    (hi, lo),
                    &mut true_env,
                    actions,
                )?;
                self.observe_range(
                    node,
                    false_guard,
                    sample,
                    fals,
                    (hi, lo),
                    &mut false_env,
                    actions,
                )?;
                for ((binding, t), f) in env.iter_mut().zip(true_env).zip(false_env) {
                    binding.value = if t.value == f.value {
                        t.value
                    } else {
                        self.ctx.ite(cond, t.value, f.value)
                    };
                    binding.known = if t.known == f.known {
                        t.known
                    } else {
                        self.ctx.ite(cond, t.known, f.known)
                    };
                }
            }
            _ => {
                if self.contains_parameter(pattern) {
                    return Err(self.unsupported(node, format!(
                        "parameter arithmetic and operators other than slices, concatenations, and ITEs are unsupported: {:?}",
                        self.ctx[pattern]
                    )));
                }
                let expected = self.ctx.slice(pattern, hi, lo);
                self.emit(actions, guard, Op::AssertEq(sample, expected));
            }
        }
        Ok(())
    }

    /// Read a range only when its parameter bits have already been captured.
    /// Slicing first avoids requiring knowledge of unrelated parameter bits.
    fn captured_range(
        &mut self,
        pattern: ExprRef,
        (hi, lo): (u32, u32),
        env: &[Binding],
    ) -> Option<ExprRef> {
        if let Some(&parameter) = self.parameter_exprs.get(&pattern) {
            let known = self.ctx.slice(env[parameter].known, hi, lo);
            let known = self.graph.simplifier.simplify(self.ctx, known);
            return (known == self.ctx.ones(hi - lo + 1))
                .then(|| self.ctx.slice(env[parameter].value, hi, lo));
        }
        if !self.contains_parameter(pattern) {
            return Some(self.ctx.slice(pattern, hi, lo));
        }
        match self.ctx[pattern].clone() {
            Expr::BVSlice { e, lo: offset, .. } => {
                self.captured_range(e, (hi + offset, lo + offset), env)
            }
            Expr::BVConcat(left, right, _) => {
                let width = right.get_bv_type(self.ctx).unwrap();
                if hi < width {
                    return self.captured_range(right, (hi, lo), env);
                }
                if lo >= width {
                    return self.captured_range(left, (hi - width, lo - width), env);
                }
                let left = self.captured_range(left, (hi - width, 0), env)?;
                let right = self.captured_range(right, (width - 1, lo), env)?;
                Some(self.ctx.concat(left, right))
            }
            Expr::BVIte { cond, tru, fals } => {
                let tru = self.captured_range(tru, (hi, lo), env)?;
                let fals = self.captured_range(fals, (hi, lo), env)?;
                Some(self.ctx.ite(cond, tru, fals))
            }
            _ => None,
        }
    }

    fn contains_addition(&self, expr: ExprRef) -> bool {
        if matches!(self.ctx[expr], Expr::BVAdd(..)) {
            return true;
        }
        let mut found = false;
        self.ctx[expr].for_each_child(|child| found |= self.contains_addition(*child));
        found
    }

    // generate the correct updates for the knownness and value registers
    fn learn(
        &mut self,
        guard: ExprRef,
        sample: ExprRef,
        parameter: usize,
        (hi, lo): (u32, u32),
        env: &mut [Binding],
        actions: &mut Vec<Action>,
    ) {
        // V = old.value, K = old.known, g = guard. V and K are the expressions
        // before this observation (to allow for simultaenous updates), including any earlier learning in this node.
        let bits = hi - lo + 1;
        let old = env[parameter];
        let width = old.value.get_bv_type(self.ctx).unwrap();
        let ctx = &mut *self.ctx;

        // Align the sampled bits with parameter bits hi:lo:
        // M = zero_extend(ones(hi - lo + 1)) << lo  (observation mask)
        // W = zero_extend(sample) << lo            (observed value)
        let ones = ctx.ones(bits);
        let mask = ctx.zero_extend(ones, width - bits);
        let observed = ctx.zero_extend(sample, width - bits);
        let shift = ctx.bit_vec_val(lo, width);
        let mask = ctx.shift_left(mask, shift);
        let observed = ctx.shift_left(observed, shift);

        // Check agreement on bits that were already known:
        // Q = K & M
        // [g] assert_eq(V & Q, W & Q)
        let overlap = ctx.and(old.known, mask);
        let lhs = ctx.and(old.value, overlap);
        let rhs = ctx.and(observed, overlap);

        // Learn only previously unknown bits: N = M & ~K.
        let not_known = ctx.not(old.known);
        let new_bits = ctx.and(mask, not_known);

        // Preserve every other value bit and fill the newly learned positions:
        // V_bound = (V & ~N) | (W & N)
        let not_new_bits = ctx.not(new_bits);
        let held = ctx.and(old.value, not_new_bits);
        let learned = ctx.and(observed, new_bits);
        let value = ctx.or(held, learned);

        // All observed bits become known: K_bound = K | M.
        let known = ctx.or(old.known, mask);

        // Apply learning only when this observation is active:
        // V_next = ite(g, V_bound, V)
        // K_next = ite(g, K_bound, K)
        env[parameter] = Binding {
            value: ctx.ite(guard, value, old.value),
            known: ctx.ite(guard, known, old.known),
        };

        // Emit the check built from V, K, and Q above. Keep those expressions
        // frozen: substituting later updates could erase an observation conflict.
        self.emit(actions, guard, Op::AssertEq(lhs, rhs));
    }
}
