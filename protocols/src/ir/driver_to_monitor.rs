//! Convert one contracted, assignment-propagated driver into a naive monitor.
//!
//! DUT assignments become observations of the sampled pins. `AssertEq` operations
//! are candidate constraints, not internal errors. Parameter values and full-width
//! knownness masks are ordinary compiler registers. All assignments read current
//! state: within a node, learning is composed through shared expressions, never
//! through intermediate registers or substitution into earlier checks.
//!
//! This module performs no knownness optimization, transaction spawning, or
//! transition-system lowering. `Fork`, `Done`, and internal errors are preserved.

use patronus::expr::{Context, Expr, ExprRef, ForEachChild, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::symbol::{SymbolId, SymbolKind, SymbolTable, Type};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::assignment_is_total;

#[derive(Clone)]
pub struct MonitorAutomaton {
    pub graph: ProtoGraph,
    /// Original argument -> generated value register.
    pub value_registers: FxHashMap<SymbolId, SymbolId>,
    /// Original argument -> physical knownness register. Simplification can
    /// remove an entry or replace its full-width mask with a Boolean register.
    /// Together these maps record ownership without relying on register names.
    pub knownness_registers: FxHashMap<SymbolId, SymbolId>,
    /// Generated register -> initial-value expression, including liveness.
    /// Register expression references are cached in `graph.symbol_expr`.
    pub register_inits: FxHashMap<SymbolId, ExprRef>,
    /// Logical full-width knownness masks at each node entry, keyed by argument.
    /// These remain available even when physical mask registers disappear.
    pub knownness_outputs: FxHashMap<NodeId, FxHashMap<SymbolId, ExprRef>>,
    /// Initialized to true. Candidate survival is interpreted by a later backend;
    /// conversion itself only emits equality constraints and parameter updates.
    pub live_register: SymbolId,
}

impl MonitorAutomaton {
    pub fn to_dot_string(&self, ctx: &Context, symbols: &SymbolTable) -> String {
        crate::ir::graphviz::to_dot_string(ctx, &self.graph, symbols)
    }
}

#[derive(Debug, Error)]
pub enum MonitorConversionError {
    #[error("unsupported monitor parameter {argument}: expected a scalar bit vector, got {tpe:?}")]
    UnsupportedParameter { argument: String, tpe: Type },
    #[error("invalid prepared driver at {node}: {reason}")]
    InvalidPreparedGraph { node: NodeId, reason: String },
    #[error("unsupported monitor expression at {node}: {reason}")]
    UnsupportedExpression { node: NodeId, reason: String },
}

/// Consumes a single-protocol graph after edge contraction, reaching definitions,
/// assignment propagation, and cleanup. Each node must contain exactly one total
/// effective assignment per DUT input (including held values and X releases).
/// Assignment action guards must be true; alternatives carry their own guards.
/// Control and ITE conditions may depend only on DUT pins and constants.
///
/// The returned graph is unoptimized. Values and masks initialize to zero, even
/// for unused parameters. Generated registers are added to the caller's symbol
/// table. On error, any registers already allocated remain in the table.
pub fn convert_driver_to_monitor(
    ctx: &mut Context,
    mut graph: ProtoGraph,
    symbols: &mut SymbolTable,
) -> Result<MonitorAutomaton, MonitorConversionError> {
    let arguments = graph.args.clone();
    let mut value_registers = FxHashMap::default();
    let mut knownness_registers = FxHashMap::default();
    let mut register_inits = FxHashMap::default();
    let mut parameter_exprs = FxHashMap::default();
    for (index, arg) in arguments.iter().enumerate() {
        let argument = arg.symbol();
        let width = match symbols[argument].tpe() {
            Type::BitVec(width) if width > 0 => width,
            tpe => {
                return Err(MonitorConversionError::UnsupportedParameter {
                    argument: symbols[argument].full_name(symbols),
                    tpe,
                });
            }
        };
        let expr = symbol_expr(ctx, &mut graph, symbols, argument);
        parameter_exprs.insert(expr, index);
        let name = symbols[argument].name().to_string();
        let value = allocate_register(
            ctx,
            &mut graph,
            symbols,
            width,
            &format!("$monitor_{name}_value"),
        );
        let known = allocate_register(
            ctx,
            &mut graph,
            symbols,
            width,
            &format!("$monitor_{name}_known"),
        );
        value_registers.insert(argument, value);
        knownness_registers.insert(argument, known);
        let zero = ctx.zero(width);
        register_inits.extend([(value, zero), (known, zero)]);
    }
    let live_register = allocate_register(ctx, &mut graph, symbols, 1, "$monitor_live");
    register_inits.insert(live_register, ctx.get_true());

    let pins: Vec<_> = graph.dut_pins(symbols).collect();
    let input_pins: FxHashSet<_> = pins
        .iter()
        .copied()
        .filter(|pin| symbols[*pin].is_in_port())
        .collect();
    let sampled_symbols = pins
        .into_iter()
        .map(|pin| symbol_expr(ctx, &mut graph, symbols, pin))
        .collect();
    let initial_env: Vec<_> = arguments
        .iter()
        .map(|arg| Binding {
            value: graph.symbol_expr(value_registers[&arg.symbol()]).unwrap(),
            known: graph
                .symbol_expr(knownness_registers[&arg.symbol()])
                .unwrap(),
        })
        .collect();
    let nodes = reachable_node_ids(ctx, &graph, graph.entry);
    let mut converter = Converter {
        ctx,
        graph: &mut graph,
        value_registers: &value_registers,
        knownness_registers: &knownness_registers,
        parameter_exprs,
        sampled_symbols,
        dependencies: FxHashMap::default(),
    };
    for node in nodes {
        converter.convert_node(node, &input_pins, &initial_env)?;
    }
    // Drop obsolete driver operations, without optimizing monitor expressions.
    graph.garbage_collect_unreachable(ctx);
    let masks = knownness_registers
        .iter()
        .map(|(&argument, &register)| (argument, graph.symbol_expr(register).unwrap()))
        .collect::<FxHashMap<_, _>>();
    let knownness_outputs = graph
        .nodes()
        .map(|(node, _)| (node, masks.clone()))
        .collect();
    Ok(MonitorAutomaton {
        graph,
        value_registers,
        knownness_registers,
        register_inits,
        knownness_outputs,
        live_register,
    })
}

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

fn allocate_register(
    ctx: &mut Context,
    graph: &mut ProtoGraph,
    symbols: &mut SymbolTable,
    width: u32,
    base: &str,
) -> SymbolId {
    // Names aid inspection; register ownership still comes only from metadata.
    // '$' is outside source identifiers. Avoid collisions with existing compiler
    // state as well, without making names depend on unrelated cached symbols.
    let mut index = 0;
    let name = loop {
        let name = if index == 0 {
            base.to_string()
        } else {
            format!("{base}_{index}")
        };
        if symbols.symbol_id_from_name_in_active_scope(&name).is_none() {
            break name;
        }
        index += 1;
    };
    let symbol = symbols.add_without_parent(name, Type::BitVec(width), SymbolKind::AutomatonState);
    symbol_expr(ctx, graph, symbols, symbol);
    symbol
}

#[derive(Clone, Copy)]
struct Binding {
    value: ExprRef,
    known: ExprRef,
}

#[derive(Clone, Copy, Default)]
struct Dependencies {
    parameter: bool,
    dont_care: bool,
}

struct Converter<'a> {
    ctx: &'a mut Context,
    graph: &'a mut ProtoGraph,
    value_registers: &'a FxHashMap<SymbolId, SymbolId>,
    knownness_registers: &'a FxHashMap<SymbolId, SymbolId>,
    parameter_exprs: FxHashMap<ExprRef, usize>,
    sampled_symbols: FxHashSet<ExprRef>,
    dependencies: FxHashMap<ExprRef, Dependencies>,
}

impl Converter<'_> {
    fn unsupported(&self, node: NodeId, reason: impl Into<String>) -> MonitorConversionError {
        MonitorConversionError::UnsupportedExpression {
            node,
            reason: reason.into(),
        }
    }

    fn deps(
        &mut self,
        node: NodeId,
        expr: ExprRef,
    ) -> Result<Dependencies, MonitorConversionError> {
        if let Some(deps) = self.dependencies.get(&expr) {
            return Ok(*deps);
        }
        let mut deps = Dependencies::default();
        if self.parameter_exprs.contains_key(&expr) {
            deps.parameter = true;
        } else if self.graph.dont_cares.contains(&expr) {
            deps.dont_care = true;
        } else {
            if matches!(self.ctx[expr], Expr::BVSymbol { .. })
                && !self.sampled_symbols.contains(&expr)
            {
                return Err(self.unsupported(
                    node,
                    "expressions may reference only this protocol's parameters and sampled DUT pins",
                ));
            }
            if expr.get_bv_type(self.ctx).is_none() {
                return Err(
                    self.unsupported(node, "only scalar bit-vector expressions are supported")
                );
            }
            let mut children = Vec::new();
            self.ctx[expr].for_each_child(|child| children.push(*child));
            for child in children {
                let child = self.deps(node, child)?;
                deps.parameter |= child.parameter;
                deps.dont_care |= child.dont_care;
            }
        }
        self.dependencies.insert(expr, deps);
        Ok(deps)
    }

    fn require_sampled(
        &mut self,
        node: NodeId,
        expr: ExprRef,
        usage: &str,
    ) -> Result<(), MonitorConversionError> {
        let deps = self.deps(node, expr)?;
        if deps.parameter {
            return Err(self.unsupported(
                node,
                format!(
                    "parameter-dependent {usage} is unsupported; use sampled DUT pins and constants"
                ),
            ));
        }
        if deps.dont_care {
            return Err(self.unsupported(node, format!("X is unsupported in {usage}")));
        }
        Ok(())
    }

    fn emit(&mut self, actions: &mut Vec<Action>, guard: ExprRef, op: Op) {
        let op = self.graph.o(op);
        actions.push(Action::new(guard, op));
    }

    fn convert_node(
        &mut self,
        node: NodeId,
        input_pins: &FxHashSet<SymbolId>,
        initial_env: &[Binding],
    ) -> Result<(), MonitorConversionError> {
        let invalid =
            |reason: String| MonitorConversionError::InvalidPreparedGraph { node, reason };
        for transition in self.graph[node].transitions.clone() {
            self.require_sampled(node, transition.guard, "transition guard")?;
            if !transition.consumes_step || !transition.rotations.is_empty() {
                return Err(invalid(
                    "expected a contracted single-protocol graph".into(),
                ));
            }
        }
        let mut env = initial_env.to_vec();
        let mut actions = Vec::new();
        let mut assigned = FxHashSet::default();
        for action in self.graph[node].actions.clone() {
            self.require_sampled(node, action.guard, "action guard")?;
            match self.graph[action.op].clone() {
                Op::Assign(pin, assignment) => {
                    if action.guard != self.ctx.get_true() {
                        return Err(invalid("assignment action guards must be true".into()));
                    }
                    if !input_pins.contains(&pin) || !assigned.insert(pin) {
                        return Err(invalid(format!(
                            "expected one effective assignment per DUT input, got {pin}"
                        )));
                    }
                    self.require_sampled(node, assignment.dont_care, "assignment guard")?;
                    for (guard, _) in &assignment.concretes {
                        self.require_sampled(node, *guard, "assignment guard")?;
                    }
                    if !assignment_is_total(self.ctx, self.graph, &assignment) {
                        return Err(invalid(format!("assignment for {pin} is not total")));
                    }
                    let sample = self.graph.symbol_expr(pin).unwrap();
                    // X wins, then the first applicable concrete alternative.
                    let mut prior = assignment.dont_care;
                    for (guard, rhs) in assignment.concretes {
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
                Op::AssertEq(lhs, rhs) => {
                    self.observe_equality(node, action.guard, lhs, rhs, &mut env, &mut actions)?;
                }
                op @ (Op::Fork | Op::Done | Op::InternalAssertFalse) => {
                    self.emit(&mut actions, action.guard, op);
                }
            }
        }
        if assigned != *input_pins {
            return Err(invalid(
                "missing effective assignments for some DUT inputs".into(),
            ));
        }
        for (index, binding) in env.into_iter().enumerate() {
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
        let left = self.deps(node, lhs)?;
        let right = self.deps(node, rhs)?;
        if left.parameter && right.parameter {
            return Err(self.unsupported(
                node,
                "relations between unresolved parameters are unsupported",
            ));
        }
        let (sample, pattern) = if left.parameter {
            (rhs, lhs)
        } else {
            (lhs, rhs)
        };
        // An effective whole-value X is a release, with no observation.
        if self.graph.dont_cares.contains(&sample) || self.graph.dont_cares.contains(&pattern) {
            return Ok(());
        }
        self.require_sampled(node, sample, "sampled side of equality")?;
        let width = pattern.get_bv_type(self.ctx).unwrap();
        if sample.get_bv_type(self.ctx) != Some(width) {
            return Err(self.unsupported(node, "equality operands must have the same bit width"));
        }
        if !left.parameter && !right.parameter && !left.dont_care && !right.dont_care {
            self.emit(actions, guard, Op::AssertEq(lhs, rhs));
            return Ok(());
        }
        self.observe_range(node, guard, sample, pattern, (width - 1, 0), env, actions)
    }

    /// Private chunk normalization: `sample` corresponds to `pattern[hi:lo]`.
    /// Slices trim ranges, and concatenation maps its right operand to low bits.
    /// No chunk is materialized as an IR operation or persistent state.
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
        if self.graph.dont_cares.contains(&pattern) {
            return Ok(());
        }
        if let Some(&parameter) = self.parameter_exprs.get(&pattern) {
            self.learn(guard, sample, parameter, (hi, lo), env, actions);
            return Ok(());
        }
        match self.ctx[pattern].clone() {
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
                self.require_sampled(node, cond, "ITE condition")?;
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
                let deps = self.deps(node, pattern)?;
                if deps.parameter {
                    return Err(self.unsupported(node, format!(
                        "parameter arithmetic and operators other than slices, concatenations, and ITEs are unsupported: {:?}",
                        self.ctx[pattern]
                    )));
                }
                self.require_sampled(node, pattern, "parameter-free equality")?;
                let expected = self.ctx.slice(pattern, hi, lo);
                self.emit(actions, guard, Op::AssertEq(sample, expected));
            }
        }
        Ok(())
    }

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
        // before this observation, including any earlier learning in this node.
        // All masks and values below have the full parameter width; &, |, and ~
        // in the formulas are bitwise operations.
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
