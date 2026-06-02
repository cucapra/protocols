// Copyright 2024-2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use anyhow::{Context, anyhow};
use baa::BitVecOps;

use crate::frontend::ast::*;
use crate::frontend::diagnostic::*;
use crate::frontend::serialize::*;
use crate::frontend::static_checks::{check_assertion_wf, check_assignment_wf, check_condition_wf};
use crate::frontend::symbol::*;

/// Helper function for emitting error messages related to invalid bit-slices
fn emit_bitslice_type_error(
    start_idx: u32,
    end_idx: u32,
    expr_width: u32,
    handler: &mut DiagnosticHandler,
    tr: &Protocol,
    expr_id: &ExprId,
) -> anyhow::Result<Type> {
    let error_msg = format!(
        "Invalid slice operation: [{}:{}] on width {}",
        start_idx, end_idx, expr_width
    );
    handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
    Err(anyhow!(error_msg))
}

/// Typechecks an expression (identified by its `ExprId`) with respect to
/// `Transaction` `tr`, `SymbolTable` `st` & the associated `DiagnosticHandler`
fn type_check_expr(
    tr: &Protocol,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    expr_id: &ExprId,
) -> anyhow::Result<Type> {
    match &tr[expr_id] {
        Expr::Const(bitvec) => {
            // Constants have bit-vector types whose length correspond
            // to the bit-width of the value
            Ok(Type::BitVec(bitvec.width()))
        }
        Expr::Sym(symid) => Ok(st[symid].tpe()),
        Expr::DontCare => Ok(Type::Unknown),
        Expr::Slice(sym_expr, msb, lsb) => {
            // To type-check `e[i:j]`, first typecheck `e` and make sure
            // it is a actually a bit-vector
            let ty = type_check_expr(tr, st, handler, sym_expr)?;
            if let Type::BitVec(expr_width) = ty {
                if msb >= lsb {
                    if *msb < expr_width {
                        let width = msb - lsb + 1;
                        Ok(Type::BitVec(width))
                    } else {
                        emit_bitslice_type_error(*msb, *lsb, expr_width, handler, tr, expr_id)
                    }
                } else {
                    let error_msg =
                        format!("Invalid slice operation: msb ({msb}) is smaller than lsb ({lsb})");
                    handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            } else {
                let error_msg = format!(
                    "Invalid slice operation: can't take bit-slices of {}",
                    serialize_type(st, ty)
                );
                handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Expr::Unary(UnaryOp::Not, not_exprid) => {
            let inner_type = type_check_expr(tr, st, handler, not_exprid)?;
            if let Type::BitVec(1) = inner_type {
                Ok(inner_type)
            } else {
                handler.emit_diagnostic_expr(
                    tr,
                    expr_id,
                    &format!(
                        "Invalid type for 'Not' expression {}",
                        serialize_type(st, inner_type)
                    ),
                    Level::Error,
                );
                Ok(inner_type)
            }
        }
        Expr::Binary(op, lhs, rhs) => {
            let lhs_type = type_check_expr(tr, st, handler, lhs)?;
            let rhs_type = type_check_expr(tr, st, handler, rhs)?;
            match op {
                BinOp::Equal => {
                    if lhs_type.is_equivalent(&rhs_type) {
                        Ok(Type::BitVec(1))
                    } else {
                        let lhs_type_str = serialize_type(st, lhs_type);
                        let rhs_type_str = serialize_type(st, rhs_type);
                        handler.emit_diagnostic_expr(
                            tr,
                            expr_id,
                            &format!(
                                "Type mismatch in binary operation: {} and {}",
                                lhs_type_str, rhs_type_str
                            ),
                            Level::Error,
                        );
                        Ok(Type::BitVec(1))
                    }
                }
                BinOp::Concat => {
                    if let (Type::BitVec(msb_w), Type::BitVec(lsb_w)) = (lhs_type, rhs_type) {
                        Ok(Type::BitVec(msb_w + lsb_w))
                    } else {
                        let lhs_type_str = serialize_type(st, lhs_type);
                        let rhs_type_str = serialize_type(st, rhs_type);
                        handler.emit_diagnostic_expr(
                            tr,
                            expr_id,
                            &format!("Cannot concatenate: {} and {}", lhs_type_str, rhs_type_str),
                            Level::Error,
                        );
                        // TODO: error!
                        Ok(Type::BitVec(1))
                    }
                }
                BinOp::Add => {
                    if let (Type::BitVec(aw), Type::BitVec(bw)) = (lhs_type, rhs_type) {
                        if aw == bw {
                            Ok(Type::BitVec(aw))
                        } else {
                            let lhs_type_str = serialize_type(st, lhs_type);
                            let rhs_type_str = serialize_type(st, rhs_type);
                            handler.emit_diagnostic_expr(
                                tr,
                                expr_id,
                                &format!("Cannot add: {} and {}", lhs_type_str, rhs_type_str),
                                Level::Error,
                            );
                            // TODO: error!
                            Ok(Type::BitVec(1))
                        }
                    } else {
                        let lhs_type_str = serialize_type(st, lhs_type);
                        let rhs_type_str = serialize_type(st, rhs_type);
                        handler.emit_diagnostic_expr(
                            tr,
                            expr_id,
                            &format!("Cannot add: {} and {}", lhs_type_str, rhs_type_str),
                            Level::Error,
                        );
                        // TODO: error!
                        Ok(Type::BitVec(1))
                    }
                }
            }
        }
        // evaluates to true or false
        Expr::IsLastIteration => Ok(Type::BitVec(1)),
        Expr::IterCount(width) => Ok(Type::BitVec(*width)),
    }
}

fn type_check_stmt(
    tr: &Protocol,
    st: &mut SymbolTable,
    handler: &mut DiagnosticHandler,
    stmt_id: &StmtId,
) -> anyhow::Result<()> {
    match &tr[stmt_id] {
        Stmt::Fork => Ok(()),
        Stmt::Step => Ok(()),
        Stmt::Assign(lhs, rhs) => {
            // First, make sure the assignment itself is well-formed
            check_assignment_wf(lhs, rhs, stmt_id, tr, st, handler)?;

            // Then, type-check the two sides of the assignment
            let lhs_type = st[lhs].tpe();
            let mut rhs_type = type_check_expr(tr, st, handler, rhs)?;
            // If the RHS type is `Unknown`, we infer it to be
            // the same type as the LHS
            if rhs_type == Type::Unknown {
                rhs_type = lhs_type;
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!(
                        "Inferred RHS type as {} from LHS type {}.",
                        serialize_type(st, rhs_type),
                        serialize_type(st, lhs_type)
                    ),
                    Level::Warning,
                );
            }
            // Check whether the LHS & RHS have equivalent types
            if lhs_type.is_equivalent(&rhs_type) {
                Ok(())
            } else {
                let expr_name = serialize_expr(tr, st, rhs);
                let error_msg = format!(
                    "Type mismatch in assignment: {} : {} and {} : {}.",
                    st[lhs].full_name(st),
                    serialize_type(st, lhs_type),
                    expr_name,
                    serialize_type(st, rhs_type)
                );
                handler.emit_diagnostic_stmt(tr, stmt_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::While(cond, bodyid) => {
            // Guards for while-loops must have type `BitVec(1)`
            let cond_type = type_check_expr(tr, st, handler, cond)?;
            if let Type::BitVec(1) = cond_type {
                // If the loop guard typechecks, make sure it is well-formed
                check_condition_wf(cond, tr, st, handler)?;

                // Then, type-check the body of the while-loop
                type_check_stmt(tr, st, handler, bodyid)
            } else {
                let error_msg = format!(
                    "Invalid type for [while] condition: {}",
                    serialize_type(st, cond_type)
                );
                handler.emit_diagnostic_expr(tr, cond, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::RepeatLoop(count_expr, bodyid) => {
            // Typecheck the no. of iterations (which must be a uint type)
            let num_iterations_type = type_check_expr(tr, st, handler, count_expr)?;
            // Temporarily allow the argument to repeat loops to have type `u8`
            // (For the purposes of the protocol for the Brave New World `axi-burst-s4` bug)
            if matches!(num_iterations_type, Type::UnsignedInt | Type::BitVec(8)) {
                // Then, type-check the loop body
                type_check_stmt(tr, st, handler, bodyid)
            } else {
                let error_msg = format!(
                    "Invalid type for no. of iterations in bounded loop: expected unsigned integer but got {} instead",
                    serialize_type(st, num_iterations_type)
                );
                handler.emit_diagnostic_expr(tr, count_expr, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::ForInLoop(id_symbol, seq_expr, bodyid) => {
            let seq_expr_tpe = type_check_expr(tr, st, handler, seq_expr)?;
            if let Type::Seq(seq_id) = seq_expr_tpe {
                let inner = st[seq_id].tpe();
                if let Type::BitVec(_) = inner {
                    // update type of id_expr to be the inner type
                    st.update_type(*id_symbol, inner);
                    // check body
                    type_check_stmt(tr, st, handler, bodyid)
                } else {
                    let error_msg = format!(
                        "Only bit-vector sequences are currently supported in loops, not {}.",
                        serialize_type(st, seq_expr_tpe)
                    );
                    handler.emit_diagnostic_expr(tr, seq_expr, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            } else {
                let error_msg = format!(
                    "Must be a sequence expression, not {}.",
                    serialize_type(st, seq_expr_tpe)
                );
                handler.emit_diagnostic_expr(tr, seq_expr, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            // Conditions for if-statement must have type `BitVec(1)`
            let cond_type = type_check_expr(tr, st, handler, cond)?;
            if let Type::BitVec(1) = cond_type {
                // If the condition typechecks, make sure it is well-formed
                check_condition_wf(cond, tr, st, handler)?;

                // Then, type-check the bodies of the `then` & `else` branches
                type_check_stmt(tr, st, handler, ifbody)?;
                type_check_stmt(tr, st, handler, elsebody)
            } else {
                let error_msg = format!(
                    "Type mismatch in If/Else condition: {}",
                    serialize_type(st, cond_type)
                );
                handler.emit_diagnostic_stmt(tr, stmt_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::AssertEq(exprid1, exprid2) => {
            // First, type-check the two arguments to `assert_eq` separately
            let expr1_type = type_check_expr(tr, st, handler, exprid1)?;
            let expr2_type = type_check_expr(tr, st, handler, exprid2)?;

            // Check that the types of both arguments are equivalent
            if expr1_type.is_equivalent(&expr2_type) {
                // Then, check that the assertion itself is well-formed
                check_assertion_wf(exprid1, exprid2, tr, st, handler)
                    .context("Ill-formed assert_eq statement")?;

                // If all the above checks pass, then the assertion both
                // type-checks and is well-formed, so it is `Ok`
                Ok(())
            } else {
                // Arguments to `assert_eq` are ill-typed, so report an error
                let expr1_name = serialize_expr(tr, st, exprid1);
                let expr2_name = serialize_expr(tr, st, exprid2);
                let error_msg = format!(
                    "Type mismatch in assert_eq: {} : {} and {} : {}.",
                    expr1_name,
                    serialize_type(st, expr1_type),
                    expr2_name,
                    serialize_type(st, expr2_type),
                );
                handler.emit_diagnostic_stmt(tr, stmt_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::Block(stmts) => {
            for stmtid in stmts {
                type_check_stmt(tr, st, handler, stmtid)?;
            }
            Ok(())
        }
    }
}

/// Typechecks every function contained in the argument `Vec`
/// of `(Transaction, SymbolTable)` pairs
pub fn type_check(
    trs: &mut [(Protocol, SymbolTable)],
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    for (tr, st) in trs {
        // debug sanity check to make sure the symbol table and the argument list are in sync
        for (index, arg) in tr.args.iter().enumerate() {
            debug_assert_eq!(st[arg].as_arg_index(), Some(index), "{}", st[arg].name());
        }

        type_check_stmt(tr, st, handler, &tr.body)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use baa::BitVecValue;
    use insta::Settings;
    use strip_ansi_escapes::strip_str;

    use super::*;
    use crate::frontend::parser::parse_file;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    fn test_helper(test_name: &str, file_name: &str) {
        let mut handler = DiagnosticHandler::default();
        let result = parse_file(file_name, &mut handler);
        let content = match result {
            Ok(mut trs) => {
                let _ = type_check(&mut trs, &mut handler);
                strip_str(handler.error_string())
            }
            Err(_) => strip_str(handler.error_string()),
        };
        snap(test_name, content);
    }

    #[test]
    fn test_add_transaction() {
        test_helper("add_d1", "tests/adders/adder_d1/add_d1.prot")
    }

    #[test]
    fn test_invalid_step_arg_transaction() {
        test_helper("invalid_step_arg", "tests/misc/invalid_step_arg.prot");
    }

    #[test]
    fn typecheck_aes128_transaction() {
        test_helper("aes128", "examples/tinyaes128/aes128.prot");
    }

    #[test]
    fn typecheck_aes128_expand_key_transaction() {
        test_helper(
            "aes128_expand_key",
            "examples/tinyaes128/aes128_expand_key.prot",
        );
    }

    #[test]
    fn typecheck_aes128_round_transaction() {
        test_helper("aes128_round", "examples/tinyaes128/aes128_round.prot");
    }

    #[test]
    fn typecheck_mul_invalid_transaction() {
        test_helper("mul_invalid", "tests/multipliers/mul_invalid.prot");
    }

    #[test]
    fn test_mul_prot() {
        test_helper("mul", "tests/multipliers/mul.prot");
    }

    #[test]
    fn typecheck_cond_transaction() {
        test_helper("cond", "tests/multipliers/mult_cond.prot");
    }

    #[test]
    fn test_calyx_go_done_transaction() {
        test_helper(
            "calyx_go_done_struct",
            "tests/calyx_go_done/calyx_go_done_struct.prot",
        );
    }

    #[test]
    fn test_simple_if_transaction() {
        test_helper("simple_if", "tests/counters/simple_if.prot");
    }

    #[test]
    fn test_simple_while_transaction() {
        test_helper("simple_while", "tests/counters/simple_while.prot");
    }

    #[test]
    fn test_simple_bounded_loop_transaction() {
        test_helper(
            "simple_bounded_loop",
            "tests/counters/simple_bounded_loop.prot",
        );
    }

    // Specific Tests
    #[test]
    fn function_argument_test() {
        let mut handler = DiagnosticHandler::default();
        let mut symbols = SymbolTable::default();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(1), SymbolKind::Arg(0));
        let b: SymbolId =
            symbols.add_without_parent("b".to_string(), Type::BitVec(1), SymbolKind::Arg(1));
        let c: SymbolId =
            symbols.add_without_parent("c".to_string(), Type::BitVec(1), SymbolKind::InPort);
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(1), SymbolKind::Arg(2));
        assert_eq!(symbols["s"], symbols[s]);
        let input =
            std::fs::read_to_string("tests/misc/func_arg_invalid.prot").expect("failed to load");
        let fileid = handler.add_file("func_arg_invalid.prot".to_string(), input);
        let mut tr = Protocol::new("func_arg_invalid".to_string());
        tr.args = vec![Arg::new(a), Arg::new(b), Arg::new(s)];

        let b_expr = tr.e(Expr::Sym(b));
        tr.add_expr_loc(b_expr, 62, 63, fileid);
        let b_expr2 = tr.e(Expr::Sym(b));
        tr.add_expr_loc(b_expr2, 84, 85, fileid);
        let zero_expr = tr.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        tr.add_expr_loc(zero_expr, 106, 107, fileid);
        let a_assign = tr.s(Stmt::Assign(a, b_expr));
        let one_expr = tr.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        tr.add_expr_loc(one_expr, 1, 1, fileid); // random location
        tr.add_stmt_loc(a_assign, 57, 64, fileid);
        let fork = tr.s(Stmt::Fork);
        tr.add_stmt_loc(fork, 68, 75, fileid);
        let c_assign = tr.s(Stmt::Assign(c, b_expr));
        tr.add_stmt_loc(c_assign, 79, 86, fileid);
        let step = tr.s(Stmt::Step);
        tr.add_stmt_loc(step, 90, 97, fileid);
        let s_assign = tr.s(Stmt::Assign(s, zero_expr));
        tr.add_stmt_loc(s_assign, 101, 108, fileid);
        let body = vec![a_assign, fork, c_assign, step, s_assign];
        tr.body = tr.s(Stmt::Block(body));
        let _ = type_check(&mut [(tr, symbols)], &mut handler);
    }
}
