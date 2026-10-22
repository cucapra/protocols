use patronus::expr::{Context, Expr, ExprRef, ForEachChild, TypeCheck};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::frontend::symbol::{SymbolId, SymbolTable, Type};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{Action, Assignment, NodeId, Op, ProtoGraph};
use crate::ir::register_simplify::{add_register, simplify_registers};

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
    // Joint construction adds liveness reads after this simplification.
    let preserved = FxHashSet::from_iter([monitor.live_register]);
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
    monitor.graph.garbage_collect_unreachable(ctx);
    monitor
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

/// Precondition: ProtoGraph is a single-protocol graph after edge contraction,
/// assignment persistence lowering/register simplification, normalization, and cleanup.
/// Each node has one total effective assignment per DUT input, including held values and X releases.
/// Expressions must pass frontend well-formedness checks.
/// TODO: Right now, we assume `allow_branch_on_arg = false`
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
    let arguments = graph.args.clone();
    let mut value_registers = FxHashMap::default();
    let mut knownness_registers = FxHashMap::default();
    let mut register_inits = FxHashMap::default();
    let mut parameter_exprs = FxHashMap::default();

    // create value and knownness registers for every parameter,
    // and initialize both to zero
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
        let value = add_register(
            ctx,
            &mut graph,
            symbols,
            &format!("$monitor_{name}_value"),
            width,
        );
        let known = add_register(
            ctx,
            &mut graph,
            symbols,
            &format!("$monitor_{name}_known"),
            width,
        );
        value_registers.insert(argument, value);
        knownness_registers.insert(argument, known);
        let zero = ctx.zero(width);
        register_inits.extend([(value, zero), (known, zero)]);
    }

    // allocate liveness register, set it to 1.
    let live_register = add_register(ctx, &mut graph, symbols, "$monitor_live", 1);
    register_inits.insert(live_register, ctx.get_true());

    // Cache pin expressions, including pins used only as assignment targets.
    let pins: Vec<_> = graph.dut_pins(symbols).collect();
    for pin in pins {
        symbol_expr(ctx, &mut graph, symbols, pin);
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

    let nodes = reachable_node_ids(ctx, &graph, graph.entry);
    let mut converter = Converter {
        ctx,
        graph: &mut graph,
        value_registers: &value_registers,
        knownness_registers: &knownness_registers,
        parameter_exprs,
        parameter_dependencies: FxHashMap::default(),
        convert_assignments,
    };

    for node in nodes {
        converter.convert_node(node, &initial_env)?;
    }
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

struct Converter<'a> {
    ctx: &'a mut Context,
    graph: &'a mut ProtoGraph,
    value_registers: &'a FxHashMap<SymbolId, SymbolId>,
    knownness_registers: &'a FxHashMap<SymbolId, SymbolId>,
    parameter_exprs: FxHashMap<ExprRef, usize>,
    parameter_dependencies: FxHashMap<ExprRef, bool>,
    convert_assignments: bool,
}

impl Converter<'_> {
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
        let mut actions = Vec::new();
        for action in self.graph[node].actions.clone() {
            match self.graph[action.op].clone() {
                // Capturing drivers still drive their inputs normally.
                op @ Op::Assign(..) if !self.convert_assignments => {
                    self.emit(&mut actions, action.guard, op);
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
                // retain all other ops as is.
                op @ (Op::Fork | Op::Done | Op::InternalAssertFalse) => {
                    self.emit(&mut actions, action.guard, op);
                }
            }
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
        // An effective whole-value X is a release, with no observation.
        if self.graph.dont_cares.contains(&lhs) || self.graph.dont_cares.contains(&rhs) {
            return Ok(());
        }
        let left_has_parameter = self.contains_parameter(lhs);
        let right_has_parameter = self.contains_parameter(rhs);
        if left_has_parameter && right_has_parameter {
            return Err(self.unsupported(
                node,
                "relations between unresolved parameters are unsupported",
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
