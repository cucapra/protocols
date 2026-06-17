// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use patronus::expr::{ExprRef, Type as PatronusType};

use crate::frontend::ast::{BinOp, Expr, ExprId, Protocol, Stmt, StmtId, UnaryOp};
use crate::frontend::symbol::{SymbolTable, Type as FrontType};
use crate::ir::proto_graph::*;

fn lower_ast_expr_to_patronus(
    ast: &Protocol,
    symbols: &SymbolTable,
    ir: &mut ProtoGraph,
    expr: ExprId,
    expected: Option<PatronusType>,
) -> ExprRef {
    let lowered = match &ast[expr] {
        Expr::DontCare => {
            let tpe = expected.unwrap_or(PatronusType::BV(1));
            let expr_ref = ir.dont_care_expr(tpe);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Const(bvv) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let expr_ref = ir.exprCtx.bv_lit(bvv);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Sym(sym) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let expr_ref = ir.lower_symbol(*sym, symbols);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Binary(BinOp::Equal, lhs, rhs) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let lhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *lhs, None);
            let rhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *rhs, None);
            let expr_ref = ir.exprCtx.equal(lhs_ref, rhs_ref);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Binary(BinOp::Concat, lhs, rhs) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let lhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *lhs, None);
            let rhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *rhs, None);
            let expr_ref = ir.exprCtx.concat(lhs_ref, rhs_ref);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Binary(BinOp::Add, lhs, rhs) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let lhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *lhs, None);
            let rhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *rhs, None);
            let expr_ref = ir.exprCtx.add(lhs_ref, rhs_ref);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Binary(BinOp::And, lhs, rhs) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let lhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *lhs, None);
            let rhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *rhs, None);
            let expr_ref = ir.exprCtx.and(lhs_ref, rhs_ref);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Unary(UnaryOp::Not, inner) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let inner_ref =
                lower_ast_expr_to_patronus(ast, symbols, ir, *inner, Some(PatronusType::BV(1)));
            let expr_ref = ir.exprCtx.not(inner_ref);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::Slice(inner, hi, lo) => {
            if let Some(expr_ref) = ir.expr_for_ast(expr) {
                return expr_ref;
            }
            let inner_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *inner, None);
            let expr_ref = ir.exprCtx.slice(inner_ref, *hi, *lo);
            ir.record_expr_mapping(expr, expr_ref);
            expr_ref
        }
        Expr::IsLastIteration => {
            panic!("loop expressions are not lowered to Patronus yet")
        }
        Expr::IterCount(_) => {
            panic!("loop expressions are not lowered to Patronus yet")
        }
    };

    lowered
}

pub fn lower_ast_to_ir(ast: Protocol, symbols: &SymbolTable) -> ProtoGraph {
    let mut ir = ProtoGraph::new(ast.ctx.clone());

    let done_node_id = ir.n(Node::empty());
    let done_op_id = ir.o(Op::Done);
    ir.push_action(done_node_id, Action::new(ir.true_id(), done_op_id));

    let body_entry = lower_stmt_to_exit(&ast, symbols, &mut ir, ast.body, done_node_id);
    ir.push_transition(ir.entry, Transition::new(ir.true_id(), body_entry, false));

    ir
}

// lower some statement `stmt_id` (which points to a subtree in the AST) to an IR
// where the final node in the IR sub-graph points to an exit node `exit`
fn lower_stmt_to_exit(
    ast: &Protocol,
    symbols: &SymbolTable,
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
                curr_exit = lower_stmt_to_exit(ast, symbols, ir, *stmt_id, curr_exit);
            }
            curr_exit
        }
        Stmt::Assign(symbol_id, expr_id) => {
            let node_id = ir.n(Node::empty());
            let rhs_ref = lower_ast_expr_to_patronus(
                ast,
                symbols,
                ir,
                *expr_id,
                Some(match symbols[*symbol_id].tpe() {
                    FrontType::BitVec(width) => PatronusType::BV(width),
                    other => panic!(
                        "unsupported assignment target type for Patronus lowering: {:?}",
                        other
                    ),
                }),
            );
            let op_id = ir.o(Op::Assign(*symbol_id, rhs_ref));
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
            let lhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *lhs, None);
            let rhs_ref = lower_ast_expr_to_patronus(ast, symbols, ir, *rhs, None);
            let op_id = ir.o(Op::AssertEq(lhs_ref, rhs_ref));
            ir.push_action(node_id, Action::new(ir.true_id(), op_id));
            ir.push_transition(node_id, Transition::new(ir.true_id(), exit, false));
            node_id
        }
        Stmt::IfElse(cond, true_branch, false_branch) => {
            // create a join node that will be the final node in the IfElse subgraph, pointing to exit
            // this will also be the target exit node for the sub-branches
            let join_node_id = ir.n(Node::empty());
            ir.push_transition(join_node_id, Transition::new(ir.true_id(), exit, false));

            let true_entry = lower_stmt_to_exit(ast, symbols, ir, *true_branch, join_node_id);
            let false_entry = lower_stmt_to_exit(ast, symbols, ir, *false_branch, join_node_id);

            // create the branch node from which we transition into the true or false entry nodes
            let branch_node_id = ir.n(Node::empty());
            let cond_ref = lower_ast_expr_to_patronus(
                ast,
                symbols,
                ir,
                *cond,
                Some(PatronusType::BV(1)),
            );
            let negated_cond = ir.exprCtx.not(cond_ref);

            // push transitions from the branch node to the true/false branch with positive/negative guarded transitions
            ir.push_transition(branch_node_id, Transition::new(cond_ref, true_entry, false));
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
            let loop_body_node_id =
                lower_stmt_to_exit(ast, symbols, ir, *loop_body, loop_guard_node_id);

            // create transitions from the loop guard to the loop body and the loop exit
            let loop_guard_ref = lower_ast_expr_to_patronus(
                ast,
                symbols,
                ir,
                *loop_guard,
                Some(PatronusType::BV(1)),
            );
            let negated_loop_guard = ir.exprCtx.not(loop_guard_ref);
            ir.push_transition(
                loop_guard_node_id,
                Transition::new(loop_guard_ref, loop_body_node_id, false),
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
