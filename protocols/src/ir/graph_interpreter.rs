// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use baa::BitVecOps;
use patronus::expr::Context;
use patronus::sim::Interpreter;
use patronus::system::TransitionSystem;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::Value;
use crate::frontend::ast::Protocol;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::interpreter::{Evaluator, ExprValue, ThreadInputValue};
use crate::ir::proto_graph::{Op, ProtoGraph};

/// interpret a `ProtoGraph`
pub fn interpret(
    pg: &ProtoGraph,
    st: &SymbolTable,
    args: FxHashMap<&str, Value>,
    ctx: &Context,
    sys: &TransitionSystem,
    sim: Interpreter,
) {
    // create a shell AST so we can reuse the existing simulator setup and expr evaluation
    let shell = Protocol::from_context(pg.ctx.clone());
    let mut evaluator = Evaluator::new(args, &shell, st, ctx, sys, sim);
    evaluator.init_thread_inputs(0).unwrap();

    let mut curr = pg.entry;
    loop {
        let node = &pg[curr];
        let mut pending_inputs: FxHashMap<SymbolId, ThreadInputValue> = FxHashMap::default();
        let mut assigned_inputs: FxHashSet<SymbolId> = FxHashSet::default();

        // note: this is more of a wellformedness check than anything.
        // even untriggered duplicate assigns to the same input in one node are rejected.
        for action in node.action_iter() {
            if let Op::Assign(symbol_id, _) = &pg[action.op]
                && !assigned_inputs.insert(*symbol_id)
            {
                panic!("multiple assigns to input {symbol_id} in one node");
            }
        }

        // first pass: buffer any triggered assigns
        for action in node.action_iter() {
            if let Op::Assign(symbol_id, expr_id) = &pg[action.op]
                && evaluate_guard(&mut evaluator, action.guard)
            {
                let value = expr_to_input_value(&mut evaluator, expr_id);
                pending_inputs.insert(*symbol_id, value);
            }
        }

        // apply inputs from the buffer
        for (symbol_id, value) in pending_inputs {
            evaluator.write_input_value_to_sim(&symbol_id, &value, true);
        }

        // second pass: after applying buffered inputs, evaluate non-assign actions
        let mut done_triggered = false;
        for action in node.action_iter() {
            if evaluate_guard(&mut evaluator, action.guard) {
                match &pg[action.op] {
                    Op::Assign(_, _) => {}
                    Op::AssertEq(lhs, rhs) => {
                        assert_eq_exprs(&mut evaluator, lhs, rhs);
                    }
                    Op::Fork => {}
                    Op::Done => done_triggered = true,
                }
            }
        }

        let satisfied_transitions: Vec<_> = node
            .transition_iter()
            .filter(|transition| evaluate_guard(&mut evaluator, transition.guard))
            .collect();

        if done_triggered {
            assert!(
                satisfied_transitions.is_empty(),
                "done triggered alongside a satisfied transition out of {curr}"
            );
            return;
        }

        if satisfied_transitions.is_empty() {
            panic!("done not triggered though there are no satisfying transitions out of {curr}");
        }

        assert!(
            satisfied_transitions.len() <= 1,
            "multiple transitions simultaneously satisfied out of {curr}"
        );

        let transition = satisfied_transitions.into_iter().next().unwrap();

        if transition.consumes_step {
            evaluator.finalize_inputs_for_cycle();
            evaluator.sim_step();
        }

        curr = transition.target;
    }
}

fn evaluate_guard(evaluator: &mut Evaluator<'_>, expr_id: crate::frontend::ast::ExprId) -> bool {
    match evaluator.evaluate_expr(&expr_id).unwrap() {
        ExprValue::Concrete(bvv) => !bvv.is_zero(),
        ExprValue::DontCare => panic!("guard evaluated to DontCare"),
    }
}

fn expr_to_input_value(
    evaluator: &mut Evaluator<'_>,
    expr_id: &crate::frontend::ast::ExprId,
) -> ThreadInputValue {
    match evaluator.evaluate_expr(expr_id).unwrap() {
        ExprValue::Concrete(bvv) => ThreadInputValue::Concrete(bvv),
        ExprValue::DontCare => ThreadInputValue::DontCare,
    }
}

fn assert_eq_exprs(
    evaluator: &mut Evaluator<'_>,
    lhs: &crate::frontend::ast::ExprId,
    rhs: &crate::frontend::ast::ExprId,
) {
    let lhs = evaluator.evaluate_expr(lhs).unwrap();
    let rhs = evaluator.evaluate_expr(rhs).unwrap();
    match (lhs, rhs) {
        (ExprValue::Concrete(lhs), ExprValue::Concrete(rhs)) => {
            assert_eq!(lhs.width(), rhs.width(), "assert_eq width mismatch");
            assert!(lhs.is_equal(&rhs), "assert_eq failed");
        }
        _ => panic!("assert_eq on DontCare"),
    }
}
