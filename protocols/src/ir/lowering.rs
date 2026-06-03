// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use std::collections::VecDeque;

use crate::frontend::ast::{Protocol, Stmt};
use crate::ir::proto_graph::*;

pub fn lower_ast_to_ir(ast: Protocol) -> ProtoGraph {
    let mut ir = ProtoGraph::new(ast.ctx.clone());

    // use a Deque for cheap FIFO
    let mut q = VecDeque::from([ast.body]);

    while let Some(stmt_id) = q.pop_front() {
        match ast[stmt_id].clone() {
            Stmt::Block(stmt_ids) => {
                q.extend(stmt_ids);
            }
            Stmt::Assign(symbol_id, expr_id) => {
                let curr_node_id = ir.n(Node::empty());
                let next_node_id = ir.next_node_id();
                let op_id = ir.o(Op::Assign(symbol_id, expr_id));
                ir.push_action(curr_node_id, Action::new(ir.true_id(), op_id));
                ir.push_transition(
                    curr_node_id,
                    Transition::new(ir.true_id(), next_node_id, false),
                );
            }
            Stmt::Step => {
                let curr_node_id = ir.n(Node::empty());
                let next_node_id = ir.next_node_id();
                ir.push_transition(
                    curr_node_id,
                    Transition::new(ir.true_id(), next_node_id, true),
                );
            }
            Stmt::Fork => {
                let curr_node_id = ir.n(Node::empty());
                let next_node_id = ir.next_node_id();
                let op_id = ir.o(Op::Fork);
                ir.push_action(curr_node_id, Action::new(ir.true_id(), op_id));
                ir.push_transition(
                    curr_node_id,
                    Transition::new(ir.true_id(), next_node_id, false),
                );
            }
            Stmt::AssertEq(lhs, rhs) => {
                let curr_node_id = ir.n(Node::empty());
                let next_node_id = ir.next_node_id();
                let op_id = ir.o(Op::AssertEq(lhs, rhs));
                ir.push_action(curr_node_id, Action::new(ir.true_id(), op_id));
                ir.push_transition(
                    curr_node_id,
                    Transition::new(ir.true_id(), next_node_id, false),
                );
            }
            Stmt::While(_expr_id, _stmt_id) => todo!(),
            Stmt::RepeatLoop(_expr_id, _stmt_id) => todo!(),
            Stmt::ForInLoop(_symbol_id, _expr_id, _stmt_id) => todo!(),
            Stmt::IfElse(_expr_id, _stmt_id, _stmt_id1) => todo!(),
        }
    }

    // the final node. this will have the done action and no
    // transitions
    let curr_node_id = ir.n(Node::empty());
    let op_id = ir.o(Op::Done);
    ir.push_action(curr_node_id, Action::new(ir.true_id(), op_id));
    ir
}
