use baa::{BitVecOps, BitVecValue, Value as BaaValue};
use patronus::expr::{
    Context, ExprRef, SerializableIrNode, SymbolValueStore, TypeCheck, eval_expr, find_symbols,
};
use rand::SeedableRng;
use rustc_hash::{FxHashMap, FxHashSet};
use std::convert::TryInto;

use crate::Value as ArgValue;
use crate::dut::{PatronusSim, PortId};
use crate::frontend::serialize::serialize_bitvec;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::interpreter::Value as WaveValue;
use crate::ir::proto_graph::{Assignment, Op, ProtoGraph};
use cranelift_entity::PrimaryMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GraphInterpretFailureKind {
    ExternalAssertion,
    InternalAssertion,
}

#[derive(Debug, Clone)]
pub struct GraphInterpretFailure {
    pub kind: GraphInterpretFailureKind,
    pub cycle: usize,
    pub message: String,
}

pub struct GraphInterpretResult {
    pub waveform: FxHashMap<PortId, Vec<WaveValue>>,
    pub failure: Option<GraphInterpretFailure>,
}

enum GraphBinding {
    Sim(PortId),
    Arg(ArgValue),
    DontCare,
}

#[derive(Debug, Clone)]
enum InputValue {
    Concrete(BitVecValue),
    DontCare,
}

struct LoopFifo {
    /// `None` if we're modeling a repeat loop
    items: Option<Vec<BitVecValue>>,
    len: u64,
    position: u64,
}

fn build_bindings(
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    args: &FxHashMap<&str, ArgValue>,
    sim: &PatronusSim,
) -> FxHashMap<ExprRef, GraphBinding> {
    let mut bindings = FxHashMap::default();

    // `symbol_expr` contains all the Args and Ports we need to bind
    for (symbol_id, expr_ref) in protocol.symbol_expr.iter() {
        if symbols[symbol_id].is_arg() {
            let arg_name = symbols[symbol_id].name();
            let value = args
                .get(arg_name)
                .unwrap_or_else(|| panic!("missing argument value for {arg_name}"))
                .clone();
            bindings.insert(*expr_ref, GraphBinding::Arg(value));
        } else if symbols[symbol_id].is_loop_var() {
            panic!("loop vars unsupported in the graph interpreter")
        } else if symbols[symbol_id].is_port() {
            bindings.insert(*expr_ref, GraphBinding::Sim(sim[*symbol_id]));
        }
    }

    for dont_care in protocol.dont_cares.iter() {
        bindings.insert(*dont_care, GraphBinding::DontCare);
    }

    bindings
}

fn build_value_store(
    ctx: &Context,
    bindings: &FxHashMap<ExprRef, GraphBinding>,
    sim: &PatronusSim,
    rng: &mut impl rand::Rng,
) -> SymbolValueStore {
    let mut store = SymbolValueStore::default();

    for (expr_ref, binding) in bindings {
        match binding {
            GraphBinding::Sim(port) => {
                let value = sim.get(*port);
                store.define_bv(*expr_ref, &value);
            }
            GraphBinding::Arg(value) => {
                let bvv: BitVecValue = value
                    .clone()
                    .try_into()
                    .unwrap_or_else(|_| panic!("unsupported argument type for {:?}", expr_ref));
                store.define_bv(*expr_ref, &bvv);
            }
            GraphBinding::DontCare => {
                let expr = &ctx[*expr_ref];
                if let Some(width) = expr.get_bv_type(ctx) {
                    let value = BitVecValue::random(rng, width);
                    store.define_bv(*expr_ref, &value);
                } else {
                    let tpe = expr.get_array_type(ctx).unwrap_or_else(|| {
                        panic!("dont-care symbol {expr_ref:?} has unsupported type")
                    });
                    store.define_array(
                        *expr_ref,
                        baa::ArrayValue::random(rng, tpe.index_width, tpe.data_width),
                    );
                }
            }
        }
    }

    store
}

/// Refresh the store with the simulator's current port values
fn read_sim_values(
    store: &mut SymbolValueStore,
    bindings: &FxHashMap<ExprRef, GraphBinding>,
    sim: &PatronusSim,
) {
    for (expr_ref, binding) in bindings {
        if let GraphBinding::Sim(port) = binding {
            store.update(*expr_ref, sim.get(*port).into());
        }
    }
}

fn update_value_store(
    ctx: &Context,
    store: &mut SymbolValueStore,
    bindings: &FxHashMap<ExprRef, GraphBinding>,
    sim: &PatronusSim,
    rng: &mut impl rand::Rng,
) {
    // get the latest sim port values, randomize DontCares
    read_sim_values(store, bindings, sim);
    for (expr_ref, binding) in bindings {
        if matches!(binding, GraphBinding::DontCare) {
            let expr = &ctx[*expr_ref];
            if let Some(width) = expr.get_bv_type(ctx) {
                let value = BitVecValue::random(rng, width);
                store.update(*expr_ref, value.into());
            } else {
                let tpe = expr.get_array_type(ctx).unwrap_or_else(|| {
                    panic!("dont-care symbol {expr_ref:?} has unsupported type")
                });
                store.update(
                    *expr_ref,
                    baa::ArrayValue::random(rng, tpe.index_width, tpe.data_width).into(),
                );
            }
        }
    }
}

fn evaluate_guard(
    ctx: &Context,
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    expr_ref: ExprRef,
) -> bool {
    if protocol.dont_cares.contains(&expr_ref) {
        panic!("guard evaluated to DontCare");
    }

    match eval_expr(ctx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => !bvv.is_zero(),
        Err(_) => panic!("guard did not evaluate to a bit-vector"),
    }
}

fn evaluate_input_value(
    ctx: &Context,
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    expr_ref: ExprRef,
) -> InputValue {
    if protocol.dont_cares.contains(&expr_ref) {
        return InputValue::DontCare;
    }

    match eval_expr(ctx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => InputValue::Concrete(bvv),
        Err(_) => panic!("assignment rhs did not evaluate to a bit-vector"),
    }
}

fn evaluate_assignment(
    ctx: &Context,
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    assignment: &Assignment,
) -> InputValue {
    if evaluate_guard(ctx, protocol, store, assignment.dont_care) {
        return InputValue::DontCare;
    }

    for (guard, rhs) in &assignment.concretes {
        if evaluate_guard(ctx, protocol, store, *guard) {
            return evaluate_input_value(ctx, protocol, store, *rhs);
        }
    }

    // TODO: make the an internal assert false
    // TODO: these should all pass after our analysis pass
    panic!("assignment did not match DontCare or any concrete branch")
}

fn evaluate_assert_equal(
    ctx: &Context,
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    lhs: ExprRef,
    rhs: ExprRef,
) -> Result<(), String> {
    if protocol.dont_cares.contains(&lhs) || protocol.dont_cares.contains(&rhs) {
        return Err("assert_eq on DontCare".to_string());
    }

    let lhs = eval_expr(ctx, store, lhs);
    let rhs = eval_expr(ctx, store, rhs);
    match (lhs, rhs) {
        (BaaValue::BitVec(lhs), BaaValue::BitVec(rhs)) => {
            assert_eq!(lhs.width(), rhs.width(), "assert_eq width mismatch");
            if !lhs.is_equal(&rhs) {
                return Err(format!(
                    "assert_eq failed: lhs={} rhs={}",
                    serialize_bitvec(&lhs, false),
                    serialize_bitvec(&rhs, false)
                ));
            }
            Ok(())
        }
        _ => Err("assert_eq on non-bit-vector values".to_string()),
    }
}

fn record_waveform(
    waveform: &mut FxHashMap<PortId, Vec<WaveValue>>,
    sim: &mut PatronusSim,
    current_inputs: &FxHashMap<PortId, WaveValue>,
    rng: &mut impl rand::Rng,
    sampled_x_ports: &FxHashSet<PortId>,
) {
    let mut dont_care_ports = FxHashSet::default();

    for input in sim.inputs().collect::<Vec<_>>() {
        let value = current_inputs
            .get(&input)
            .unwrap_or(&WaveValue::DontCare)
            .clone();
        match value {
            WaveValue::Concrete(bvv) => {
                sim.set(input, &bvv);
                waveform
                    .entry(input)
                    .or_default()
                    .push(WaveValue::Concrete(bvv));
            }
            WaveValue::DontCare => {
                if !sampled_x_ports.contains(&input) {
                    let random_val = BitVecValue::random(rng, sim.port_width(input));
                    sim.set(input, &random_val);
                }
                waveform.entry(input).or_default().push(WaveValue::DontCare);
                dont_care_ports.insert(input);
            }
        }
    }

    for output in sim.outputs() {
        let value = if sim
            .coi_inputs(output)
            .any(|input| dont_care_ports.contains(&input))
        {
            WaveValue::DontCare
        } else {
            WaveValue::Concrete(sim.get(output))
        };
        waveform.entry(output).or_default().push(value);
    }
}

/// interpret a `ProtoGraph` using Patronus expressions directly.
pub fn interpret(
    ctx: &Context,
    pg: &ProtoGraph,
    st: &SymbolTable,
    args: FxHashMap<&str, ArgValue>,
    sim: &mut PatronusSim,
) -> GraphInterpretResult {
    let mut waveform = FxHashMap::default();
    let mut current_inputs =
        FxHashMap::from_iter(sim.inputs().map(|port| (port, WaveValue::DontCare)));

    let bindings = build_bindings(pg, st, &args, sim);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let mut store = build_value_store(ctx, &bindings, sim, &mut rng);

    // get the initial values for registers
    for (&register, &init) in &pg.register_inits {
        let value = eval_expr(ctx, &store, init);
        let BaaValue::BitVec(value) = value else {
            unreachable!("register was not initialized.")
        };
        store.define_bv(pg.symbol_expr(register).unwrap(), &value);
    }

    // set up fifos for each loop
    let mut fifos = PrimaryMap::new();
    for (id, inputs) in pg.loops.iter() {
        // if a for-in loop, get the sequence arg
        let items = inputs.source.argument.map(|argument| {
            Vec::<BitVecValue>::try_from(args[st[argument].name()].clone())
                .expect("loop item argument must be a sequence")
        });
        // if a repeat loop, get the length of the loop
        let len = match inputs.source.length {
            Some(length) => eval_expr(ctx, &store, length)
                .try_into_u64()
                .expect("sequence length must fit in u64"),
            None => items.as_ref().unwrap().len() as u64,
        };
        assert_eq!(
            fifos.push(LoopFifo {
                items,
                len,
                position: 0
            }),
            id
        );
        for input in [inputs.data, inputs.last, inputs.valid] {
            store.define_bv(input, &BitVecValue::zero(input.get_bv_type(ctx).unwrap()));
        }
    }
    // what loops should be moved forward at the end of this cycle?
    let mut pending_pops = FxHashSet::default();

    let mut curr = pg.entry;
    let mut cycle = 0;
    loop {
        read_sim_values(&mut store, &bindings, sim);

        // for every loop, update data(), last(), and valid()
        for (id, inputs) in pg.loops.iter() {
            let fifo = &fifos[id];
            let data = fifo
                .items
                .as_ref()
                .and_then(|items| items.get(fifo.position as usize))
                .cloned()
                .unwrap_or_else(|| BitVecValue::zero(inputs.data.get_bv_type(ctx).unwrap()));
            store.update(inputs.data, data.into());
            store.update(
                inputs.last,
                BitVecValue::from_u64(
                    u64::from(fifo.position < fifo.len && fifo.position + 1 == fifo.len),
                    1,
                )
                .into(),
            );
            store.update(
                inputs.valid,
                BitVecValue::from_u64(u64::from(fifo.position < fifo.len), 1).into(),
            );
        }

        let node = &pg[curr];
        let mut pending_inputs: FxHashMap<SymbolId, InputValue> = FxHashMap::default();
        let mut pending_registers = Vec::new();
        let mut sampled_x_ports = FxHashSet::default();

        {
            for action in &node.actions {
                if let Op::Assign(symbol_id, assignment) = &pg[action.op]
                    && st[*symbol_id].is_in_port()
                {
                    assert_eq!(
                        action.guard,
                        ctx.get_true(),
                        "assignment action guards must be 1; path conditions belong in Assignment"
                    );
                    let value = evaluate_assignment(ctx, pg, &store, assignment);

                    pending_inputs.insert(*symbol_id, value);
                }
            }
        }

        for (symbol_id, value) in pending_inputs {
            let port = sim[symbol_id];
            match value {
                InputValue::Concrete(bvv) => {
                    sim.set(port, &bvv);
                    current_inputs.insert(port, WaveValue::Concrete(bvv));
                }
                InputValue::DontCare => {
                    let name = format!("dont_care.{}", st[symbol_id].name());
                    let expr = pg
                        .dont_cares
                        .iter()
                        .find(|&&e| ctx[e].get_symbol_name(ctx) == Some(name.as_str()));
                    if let Some(&expr) = expr {
                        let value: BitVecValue = eval_expr(ctx, &store, expr).try_into().unwrap();
                        sim.set(port, &value);
                        sampled_x_ports.insert(port);
                    } else if !matches!(current_inputs.get(&port), Some(WaveValue::DontCare)) {
                        let value = BitVecValue::random(&mut rng, st[symbol_id].tpe().bitwidth());
                        sim.set(port, &value);
                    }
                    current_inputs.insert(port, WaveValue::DontCare);
                }
            }
        }

        read_sim_values(&mut store, &bindings, sim);
        for action in &node.actions {
            if let Op::Assign(register, assignment) = pg[action.op].clone()
                && pg.register_inits.contains_key(&register)
                && evaluate_guard(ctx, pg, &store, action.guard)
            {
                assert_eq!(assignment.dont_care, ctx.get_false());
                let held = pg.symbol_expr(register).unwrap();
                let mut value = held;
                for &(guard, rhs) in assignment.concretes.iter().rev() {
                    if evaluate_guard(ctx, pg, &store, guard) {
                        value = rhs;
                    }
                }
                pending_registers.push((register, eval_expr(ctx, &store, value)));
            }
        }

        let mut done_triggered = false;
        for action in &node.actions {
            if evaluate_guard(ctx, pg, &store, action.guard) {
                match &pg[action.op] {
                    Op::Assign(_, _) => {}
                    Op::AssertEq(lhs, rhs) => {
                        if let Err(message) = evaluate_assert_equal(ctx, pg, &store, *lhs, *rhs) {
                            return GraphInterpretResult {
                                waveform,
                                failure: Some(GraphInterpretFailure {
                                    kind: GraphInterpretFailureKind::ExternalAssertion,
                                    cycle,
                                    message,
                                }),
                            };
                        }
                    }
                    Op::Fork => {}
                    Op::InternalAssertFalse => {
                        return GraphInterpretResult {
                            waveform,
                            failure: Some(GraphInterpretFailure {
                                kind: GraphInterpretFailureKind::InternalAssertion,
                                cycle,
                                message: format!(
                                    "internal assertion failed at graph node {curr}: guard {} evaluated true",
                                    ctx[action.guard].serialize_to_str(ctx)
                                ),
                            }),
                        };
                    }
                    Op::Done => done_triggered = true,
                }
            }
        }

        let satisfied_transitions: Vec<_> = node
            .transitions
            .iter()
            .filter(|transition| evaluate_guard(ctx, pg, &store, transition.guard))
            .collect();

        if done_triggered {
            // FIXME: we don't handle done properly for concrete trace lowering.
            // this assertion is also guaranteed not to fire for the symbolic lowering
            // so it's not useful for now.
            // assert!(
            //     satisfied_transitions.is_empty()
            //         || !done_triggered && !satisfied_transitions.is_empty(),
            //     "done triggered alongside a satisfied transition out of {curr}"
            // );
        }

        assert!(
            satisfied_transitions.len() <= 1,
            "non-determinism found: multiple transitions simultaneously satisfied out of {curr}"
        );

        for (register, value) in pending_registers {
            store.update(pg.symbol_expr(register).unwrap(), value);
        }
        match satisfied_transitions.into_iter().next() {
            Some(t) => {
                // Check if we're entering a new loop iteration
                // This occurs <===> we evaluate fifo.valid to true in this cycle
                let inputs = find_symbols(ctx, t.guard);
                for (id, fifo) in pg.loops.iter() {
                    if inputs.contains(&fifo.valid)
                        && evaluate_guard(ctx, pg, &store, fifo.valid)
                    {
                        pending_pops.insert(id);
                    }
                }
                if t.consumes_step {
                    record_waveform(
                        &mut waveform,
                        sim,
                        &current_inputs,
                        &mut rng,
                        &sampled_x_ports,
                    );
                    // Pops pending FIFOs on the step-edge.
                    for id in pending_pops.drain() {
                        fifos[id].position += 1;
                    }
                    sim.step();
                    update_value_store(ctx, &mut store, &bindings, sim, &mut rng);
                    cycle += 1;
                }
                curr = t.target;
            }
            None => break,
        }
    }

    GraphInterpretResult {
        waveform,
        failure: None,
    }
}

#[cfg(test)]
#[path = "graph_interpreter_tests.rs"]
mod tests;
