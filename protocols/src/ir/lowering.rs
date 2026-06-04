// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use crate::frontend::ast::{Expr, Protocol, Stmt, StmtId, UnaryOp};
use crate::ir::proto_graph::*;

pub fn lower_ast_to_ir(ast: Protocol) -> ProtoGraph {
    let mut ir = ProtoGraph::new(ast.ctx.clone());

    let done_node_id = ir.n(Node::empty());
    let done_op_id = ir.o(Op::Done);
    ir.push_action(done_node_id, Action::new(ir.true_id(), done_op_id));

    let body_entry = lower_stmt_to_exit(&ast, &mut ir, ast.body, done_node_id);
    ir.push_transition(ir.entry, Transition::new(ir.true_id(), body_entry, false));

    ir
}

// lower some statement `stmt_id` (which points to a subtree in the AST) to an IR
// where the final node in the IR sub-graph points to an exit node `exit`
fn lower_stmt_to_exit(
    ast: &Protocol,
    ir: &mut ProtoGraph,
    stmt_id: StmtId,
    exit: NodeId,
) -> NodeId {
    match &ast[stmt_id] {
        Stmt::Block(stmt_ids) => {
            if stmt_ids.is_empty() {
                let node_id = ir.n(Node::empty());
                ir.push_transition(node_id, Transition::new(ir.true_id(), exit, false));
                return node_id;
            }

            let mut curr_exit = exit;
            for stmt_id in stmt_ids.iter().rev() {
                curr_exit = lower_stmt_to_exit(ast, ir, *stmt_id, curr_exit);
            }
            curr_exit
        }
        Stmt::Assign(symbol_id, expr_id) => {
            let node_id = ir.n(Node::empty());
            let op_id = ir.o(Op::Assign(*symbol_id, *expr_id));
            ir.push_action(node_id, Action::new(ir.true_id(), op_id));
            ir.push_transition(node_id, Transition::new(ir.true_id(), exit, false));
            node_id
        }
        Stmt::Step => {
            let node_id = ir.n(Node::empty());
            ir.push_transition(node_id, Transition::new(ir.true_id(), exit, true));
            node_id
        }
        Stmt::Fork => {
            let node_id = ir.n(Node::empty());
            let op_id = ir.o(Op::Fork);
            ir.push_action(node_id, Action::new(ir.true_id(), op_id));
            ir.push_transition(node_id, Transition::new(ir.true_id(), exit, false));
            node_id
        }
        Stmt::AssertEq(lhs, rhs) => {
            let node_id = ir.n(Node::empty());
            let op_id = ir.o(Op::AssertEq(*lhs, *rhs));
            ir.push_action(node_id, Action::new(ir.true_id(), op_id));
            ir.push_transition(node_id, Transition::new(ir.true_id(), exit, false));
            node_id
        }
        Stmt::IfElse(cond, true_branch, false_branch) => {
            // create a join node that will be the final node in the IfElse subgraph, pointing to exit
            // this will also be the target exit node for the sub-branches
            let join_node_id = ir.n(Node::empty());
            ir.push_transition(join_node_id, Transition::new(ir.true_id(), exit, false));

            let true_entry = lower_stmt_to_exit(ast, ir, *true_branch, join_node_id);
            let false_entry = lower_stmt_to_exit(ast, ir, *false_branch, join_node_id);

            // create the branch node from which we transition into the true or false entry nodes
            let branch_node_id = ir.n(Node::empty());
            let negated_cond = ir.e(Expr::Unary(UnaryOp::Not, *cond));

            // push transitions from the branch node to the true/false branch with positive/negative guarded transitions
            ir.push_transition(branch_node_id, Transition::new(*cond, true_entry, false));
            ir.push_transition(
                branch_node_id,
                Transition::new(negated_cond, false_entry, false),
            );
            branch_node_id
        }
        // FIXME: not sure if there is a better word than "guard" here. worried about overloading that term.
        // maybe just "cond"?
        Stmt::While(loop_guard, loop_body) => {
            let loop_exit_node_id = ir.n(Node::empty());
            ir.push_transition(
                loop_exit_node_id,
                Transition::new(ir.true_id(), exit, false),
            );

            // create the loop guard.node from which we transition into the loop body or loop exit nodes
            let loop_guard_node_id = ir.n(Node::empty());

            // lower the loop body, which exits into the loop guard (the cycle-forming edge)
            let loop_body_node_id = lower_stmt_to_exit(ast, ir, *loop_body, loop_guard_node_id);

            // create transitions from the loop guard to the loop body and the loop exit
            let negated_loop_guard = ir.e(Expr::Unary(UnaryOp::Not, *loop_guard));
            ir.push_transition(
                loop_guard_node_id,
                Transition::new(*loop_guard, loop_body_node_id, false),
            );
            ir.push_transition(
                loop_guard_node_id,
                Transition::new(negated_loop_guard, loop_exit_node_id, false),
            );

            loop_guard_node_id
        }
        Stmt::RepeatLoop(_expr_id, _stmt_id) => todo!(),
        Stmt::ForInLoop(_symbol_id, _expr_id, _stmt_id) => todo!(),
    }
}