use std::convert::TryInto;

use baa::{BitVecOps, BitVecValue, Value as BaaValue};
use patronus::expr::{ExprRef, SymbolValueStore, TypeCheck, eval_expr};
use rand::SeedableRng;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::Value;
use crate::dut::{PatronusSim, PortId};
use crate::frontend::serialize::serialize_bitvec;
use crate::frontend::symbol::{SymbolId, SymbolTable, Type};
use crate::ir::proto_graph::{Op, ProtoGraph};

enum GraphBinding {
    Sim(PortId),
    Arg(Value),
    DontCare,
}

#[derive(Debug, Clone)]
enum InputValue {
    Concrete(BitVecValue),
    DontCare,
}

fn build_bindings(
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    args: &FxHashMap<&str, Value>,
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
    protocol: &ProtoGraph,
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
                let expr = &protocol.expr_ctx[*expr_ref];
                if let Some(width) = expr.get_bv_type(&protocol.expr_ctx) {
                    let value = BitVecValue::random(rng, width);
                    store.define_bv(*expr_ref, &value);
                } else {
                    let tpe = expr.get_array_type(&protocol.expr_ctx).unwrap_or_else(|| {
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
    store: &mut SymbolValueStore,
    protocol: &ProtoGraph,
    bindings: &FxHashMap<ExprRef, GraphBinding>,
    sim: &PatronusSim,
    rng: &mut impl rand::Rng,
) {
    // get the latest sim port values, randomize DontCares
    read_sim_values(store, bindings, sim);
    for (expr_ref, binding) in bindings {
        if matches!(binding, GraphBinding::DontCare) {
            let expr = &protocol.expr_ctx[*expr_ref];
            if let Some(width) = expr.get_bv_type(&protocol.expr_ctx) {
                let value = BitVecValue::random(rng, width);
                store.update(*expr_ref, value.into());
            } else {
                let tpe = expr.get_array_type(&protocol.expr_ctx).unwrap_or_else(|| {
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

fn evaluate_guard(protocol: &ProtoGraph, store: &SymbolValueStore, expr_ref: ExprRef) -> bool {
    if protocol.dont_cares.contains(&expr_ref) {
        panic!("guard evaluated to DontCare");
    }

    match eval_expr(&protocol.expr_ctx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => !bvv.is_zero(),
        Err(_) => panic!("guard did not evaluate to a bit-vector"),
    }
}

fn evaluate_input_value(
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    expr_ref: ExprRef,
) -> InputValue {
    if protocol.dont_cares.contains(&expr_ref) {
        return InputValue::DontCare;
    }

    match eval_expr(&protocol.expr_ctx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => InputValue::Concrete(bvv),
        Err(_) => panic!("assignment rhs did not evaluate to a bit-vector"),
    }
}

fn evaluate_assert_equal(
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    lhs: ExprRef,
    rhs: ExprRef,
) {
    if protocol.dont_cares.contains(&lhs) || protocol.dont_cares.contains(&rhs) {
        panic!("assert_eq on DontCare");
    }

    let lhs = eval_expr(&protocol.expr_ctx, store, lhs);
    let rhs = eval_expr(&protocol.expr_ctx, store, rhs);
    match (lhs, rhs) {
        (BaaValue::BitVec(lhs), BaaValue::BitVec(rhs)) => {
            assert_eq!(lhs.width(), rhs.width(), "assert_eq width mismatch");
            assert!(
                lhs.is_equal(&rhs),
                "assert_eq failed: lhs={} rhs={}",
                serialize_bitvec(&lhs, false),
                serialize_bitvec(&rhs, false)
            );
        }
        _ => panic!("assert_eq on non-bit-vector values"),
    }
}

/// interpret a `ProtoGraph` using Patronus expressions directly.
pub fn interpret(
    pg: &ProtoGraph,
    st: &SymbolTable,
    args: FxHashMap<&str, Value>,
    sim: &mut PatronusSim,
) {
    let bindings = build_bindings(pg, st, &args, sim);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    let mut store = build_value_store(pg, &bindings, sim, &mut rng);

    let mut curr = pg.entry;
    loop {
        read_sim_values(&mut store, &bindings, sim);

        let node = &pg[curr];
        let mut pending_inputs: FxHashMap<SymbolId, InputValue> = FxHashMap::default();
        let mut assigned_inputs: FxHashSet<SymbolId> = FxHashSet::default();

        for action in &node.actions {
            if let Op::Assign(symbol_id, _) = &pg[action.op]
                && !assigned_inputs.insert(*symbol_id)
            {
                panic!("multiple assigns to input {symbol_id} in one node");
            }
        }

        {
            for action in &node.actions {
                if let Op::Assign(symbol_id, expr_ref) = &pg[action.op]
                    && evaluate_guard(pg, &store, action.guard)
                {
                    let value = evaluate_input_value(pg, &store, *expr_ref);

                    pending_inputs.insert(*symbol_id, value);
                }
            }
        }

        for (symbol_id, value) in pending_inputs {
            let port = sim[symbol_id];
            match value {
                InputValue::Concrete(bvv) => sim.set(port, &bvv),
                InputValue::DontCare => {
                    let width = match st[symbol_id].tpe() {
                        Type::BitVec(w) => w,
                        _ => panic!("expected BitVec type for input {symbol_id}"),
                    };
                    let random_val = BitVecValue::random(&mut rng, width);
                    sim.set(port, &random_val);
                }
            }
        }

        update_value_store(&mut store, pg, &bindings, sim, &mut rng);

        let mut done_triggered = false;
        for action in &node.actions {
            if evaluate_guard(pg, &store, action.guard) {
                match &pg[action.op] {
                    Op::Assign(_, _) => {}
                    Op::AssertEq(lhs, rhs) => {
                        evaluate_assert_equal(pg, &store, *lhs, *rhs);
                    }
                    Op::Fork => {}
                    Op::InternalAssertFalse => panic!("internal assert failed"),
                    Op::Done => done_triggered = true,
                }
            }
        }

        let satisfied_transitions: Vec<_> = node
            .transitions
            .iter()
            .filter(|transition| evaluate_guard(pg, &store, transition.guard))
            .collect();

        assert!(
            done_triggered && satisfied_transitions.is_empty()
                || !done_triggered && !satisfied_transitions.is_empty(),
            "done triggered alongside a satisfied transition out of {curr}"
        );
        assert!(
            satisfied_transitions.len() <= 1,
            "multiple transitions simultaneously satisfied out of {curr}"
        );

        match satisfied_transitions.into_iter().next() {
            Some(t) => {
                if t.consumes_step {
                    sim.step();
                }
                curr = t.target;
            }
            None => break,
        }
    }
}
