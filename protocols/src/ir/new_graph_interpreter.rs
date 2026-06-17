use std::convert::TryInto;

use baa::{BitVecOps, BitVecValue, Value as BaaValue};
use patronus::expr::{Context, ExprRef, SymbolValueStore, eval_expr};
use patronus::sim::{Interpreter, Simulator};
use patronus::system::TransitionSystem;
use rand::SeedableRng;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::frontend::symbol::{SymbolId, SymbolTable, Type};
use crate::ir::proto_graph::{Op, ProtoGraph};
use crate::Value;

enum GraphBinding {
    System(ExprRef),
    Arg(Value),
    DontCare,
}

#[derive(Debug, Clone)]
enum InputValue{
    Concrete(BitVecValue),
    DontCare,
}

fn is_dontcare_expr(protocol: &ProtoGraph, expr_ref: ExprRef) -> bool {
    protocol
        .exprCtx
        .get_symbol_name(expr_ref)
        .is_some_and(|name| name.starts_with("__dontcare_"))
}

fn build_bindings(
    protocol: &ProtoGraph,
    symbols: &SymbolTable,
    args: &FxHashMap<&str, Value>,
    signal_names: &FxHashMap<String, ExprRef>,
) -> FxHashMap<ExprRef, GraphBinding> {
    let mut bindings = FxHashMap::default();

    for idx in 0..protocol.exprCtx.num_exprs() {
        let expr_ref = ExprRef::from_index(idx);
        let Some(name) = protocol.exprCtx.get_symbol_name(expr_ref) else {
            continue;
        };

        if name.starts_with("__dontcare__") {
            bindings.insert(expr_ref, GraphBinding::DontCare);
            continue;
        }

        let Some(symbol_id) = symbols.symbol_id_from_name(name) else {
            continue;
        };

        if symbols[symbol_id].is_arg() {
            let arg_name = symbols[symbol_id].name();
            let value = args
                .get(arg_name)
                .unwrap_or_else(|| panic!("missing argument value for {arg_name}"))
                .clone();
            bindings.insert(expr_ref, GraphBinding::Arg(value));
        } else if symbols[symbol_id].is_port() || symbols[symbol_id].is_loop_var() {
            let system_expr = signal_names
                .get(name)
                .copied()
                .unwrap_or_else(|| panic!("missing simulator signal for {name}"));
            bindings.insert(expr_ref, GraphBinding::System(system_expr));
        }
    }

    bindings
}

fn build_value_store(
    bindings: &FxHashMap<ExprRef, GraphBinding>,
    sim: &Interpreter,
) -> SymbolValueStore {
    let mut store = SymbolValueStore::default();

    for (expr_ref, binding) in bindings {
        if matches!(binding, GraphBinding::DontCare) {
            continue;
        }

        let value = match binding {
            GraphBinding::System(sys_expr) => sim.get(*sys_expr),
            GraphBinding::Arg(value) => {
                let bvv: BitVecValue = value
                    .clone()
                    .try_into()
                    .unwrap_or_else(|_| panic!("unsupported argument type for {:?}", expr_ref));
                BaaValue::BitVec(bvv)
            }
            GraphBinding::DontCare => unreachable!(),
        };

        match value {
            BaaValue::BitVec(bv) => store.define_bv(*expr_ref, &bv),
            BaaValue::Array(arr) => store.define_array(*expr_ref, arr),
        }
    }

    store
}

fn evaluate_guard(protocol: &ProtoGraph, store: &SymbolValueStore, expr_ref: ExprRef) -> bool {
    if is_dontcare_expr(protocol, expr_ref) {
        panic!("guard evaluated to DontCare");
    }

    match eval_expr(&protocol.exprCtx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => !bvv.is_zero(),
        Err(_) => panic!("guard did not evaluate to a bit-vector"),
    }
}

fn evaluate_input_value(
    protocol: &ProtoGraph,
    store: &SymbolValueStore,
    expr_ref: ExprRef,
) -> InputValue {
    if is_dontcare_expr(protocol, expr_ref) {
        return InputValue::DontCare;
    }

    match eval_expr(&protocol.exprCtx, store, expr_ref).try_into() {
        Ok::<BitVecValue, _>(bvv) => InputValue::Concrete(bvv),
        Err(_) => panic!("assignment rhs did not evaluate to a bit-vector"),
    }
}

fn assert_eq_exprs(protocol: &ProtoGraph, store: &SymbolValueStore, lhs: ExprRef, rhs: ExprRef) {
    if is_dontcare_expr(protocol, lhs) || is_dontcare_expr(protocol, rhs) {
        panic!("assert_eq on DontCare");
    }

    let lhs = eval_expr(&protocol.exprCtx, store, lhs);
    let rhs = eval_expr(&protocol.exprCtx, store, rhs);
    match (lhs, rhs) {
        (BaaValue::BitVec(lhs), BaaValue::BitVec(rhs)) => {
            assert_eq!(lhs.width(), rhs.width(), "assert_eq width mismatch");
            assert!(lhs.is_equal(&rhs), "assert_eq failed");
        }
        _ => panic!("assert_eq on non-bit-vector values"),
    }
}

/// interpret a `ProtoGraph` using Patronus expressions directly.
pub fn interpret(
    pg: &ProtoGraph,
    st: &SymbolTable,
    args: FxHashMap<&str, Value>,
    sim_ctx: &Context,
    sys: &TransitionSystem,
    mut sim: Interpreter,
) {
    let signal_names = sys.get_name_map(sim_ctx);
    let bindings = build_bindings(pg, st, &args, &signal_names);
    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    sim.init(patronus::sim::InitKind::Zero);

    let mut curr = pg.entry;
    loop {
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
            let store = build_value_store(&bindings, &sim);

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
            let signal_expr = signal_names
                .get(st.full_name_from_symbol_id(&symbol_id).as_str())
                .copied()
            .unwrap_or_else(|| {
                panic!(
                    "missing simulator signal for {}",
                    st.full_name_from_symbol_id(&symbol_id)
                )
            });
            match value {
                InputValue::Concrete(bvv) => sim.set(signal_expr, &bvv),
                InputValue::DontCare => {
                    let width = match st[symbol_id].tpe() {
                        Type::BitVec(w) => w,
                        _ => panic!("expected BitVec type for input {symbol_id}"),
                    };
                    let random_val = BitVecValue::random(&mut rng, width);
                    sim.set(signal_expr, &random_val);
                }
            }
        }

        let store = build_value_store(&bindings, &sim);

        let mut done_triggered = false;
        for action in &node.actions {
            if evaluate_guard(pg, &store, action.guard) {
                match &pg[action.op] {
                    Op::Assign(_, _) => {}
                    Op::AssertEq(lhs, rhs) => {
                        assert_eq_exprs(pg, &store, *lhs, *rhs);
                    }
                    Op::Fork => {}
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
