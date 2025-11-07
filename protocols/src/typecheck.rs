// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use anyhow::anyhow;
use baa::BitVecOps;
use std::cmp::Ordering::{Equal, Greater, Less};

use crate::{diagnostic::*, ir::*, serialize::*};

/// Helper function for emitting error messages related to invalid bit-slices
fn emit_bitslice_type_error(
    start_idx: u32,
    end_idx: u32,
    expr_width: u32,
    handler: &mut DiagnosticHandler,
    tr: &Transaction,
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
fn check_expr_types(
    tr: &Transaction,
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
        Expr::Slice(sym_expr, start_idx, end_idx) => {
            // To type-check `e[i:j]`, first typecheck `e` and make sure
            // it is a actually a bit-vector
            let ty = check_expr_types(tr, st, handler, sym_expr)?;
            match ty {
                Type::BitVec(expr_width) => match start_idx.cmp(end_idx) {
                    Equal => Ok(Type::BitVec(1)),
                    Greater => {
                        // Make sure the width of the bitslice is at most
                        // the width of the entire bit-vector
                        let slice_width = start_idx - end_idx;
                        if slice_width <= expr_width {
                            Ok(Type::BitVec(slice_width))
                        } else {
                            emit_bitslice_type_error(
                                *start_idx, *end_idx, expr_width, handler, tr, expr_id,
                            )
                        }
                    }
                    Less => {
                        // Emit an error message when `i < j` in `e[i:j]`
                        // (we expect `i >= j`,
                        // since `i` is the MSB & `j` is the LSB)
                        let error_msg = format!(
                            "Invalid slice operation: [{}:{}] on width {} (MSB {} is less than LSB {}, which is the other way round)",
                            start_idx, end_idx, expr_width, start_idx, end_idx
                        );
                        handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                        Err(anyhow!(error_msg))
                    }
                },
                Type::Struct(struct_id) => {
                    let error_msg = format!(
                        "Invalid slice operation: can't take bit-slices of struct {}",
                        st[struct_id].name()
                    );
                    handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
                Type::Unknown => {
                    let error_msg = format!(
                        "Invalid slice operation: can't take bit-slices of expr {} with Unknown type",
                        serialize_expr(tr, st, expr_id)
                    );
                    handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            }
        }
        Expr::Unary(UnaryOp::Not, not_exprid) => {
            let inner_type = check_expr_types(tr, st, handler, not_exprid)?;
            if let Type::BitVec(1) = inner_type {
                Ok(inner_type)
            } else {
                handler.emit_diagnostic_expr(
                    tr,
                    expr_id,
                    &format!(
                        "Invalid type for 'Not' expression {}",
                        serialize_type(st, inner_type)
                    )
                    .to_string(),
                    Level::Error,
                );
                Ok(inner_type)
            }
        }
        Expr::Binary(BinOp::Concat, lhs, rhs) | Expr::Binary(BinOp::Equal, lhs, rhs) => {
            let lhs_type = check_expr_types(tr, st, handler, lhs)?;
            let rhs_type = check_expr_types(tr, st, handler, rhs)?;
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
    }
}

fn check_stmt_types(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    stmt_id: &StmtId,
) -> anyhow::Result<()> {
    match &tr[stmt_id] {
        Stmt::Fork => Ok(()),
        Stmt::Step => Ok(()),
        Stmt::Assign(lhs, rhs) => {
            // Function argument cannot be assigned
            if tr.args.iter().any(|arg| arg.symbol() == *lhs) {
                let error_msg = "Cannot assign to function argument. Try using assert_eq if you want to check the value of a transaction output.";
                handler.emit_diagnostic_stmt(tr, stmt_id, error_msg, Level::Error);
                return Err(anyhow!(error_msg));
            }
            // DUT output cannot be assigned
            if let Some(parent) = st[lhs].parent() {
                if let Type::Struct(structid) = st[parent].tpe() {
                    let fields = st[structid].pins();
                    if fields
                        .iter()
                        .any(|field| field.dir() == Dir::Out && field.name() == st[lhs].name())
                    {
                        let error_msg = format!(
                            "{} is an output port of {} and thus cannot be assigned.",
                            st[lhs].full_name(st),
                            st[parent].name()
                        );
                        handler.emit_diagnostic_stmt(tr, stmt_id, &error_msg, Level::Error);
                        return Err(anyhow!(error_msg));
                    }
                }
            }
            let lhs_type = st[lhs].tpe();
            let mut rhs_type = check_expr_types(tr, st, handler, rhs)?;
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
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            // Guards for while-loops must have type `BitVec(1)`
            if let Type::BitVec(1) = cond_type {
                check_stmt_types(tr, st, handler, bodyid)
            } else {
                let error_msg = format!(
                    "Invalid type for [while] condition: {}",
                    serialize_type(st, cond_type)
                );
                handler.emit_diagnostic_expr(tr, cond, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            // Guards for conditions must have type `BitVec(1)`
            if let Type::BitVec(1) = cond_type {
                check_stmt_types(tr, st, handler, ifbody)?;
                check_stmt_types(tr, st, handler, elsebody)?;
                Ok(())
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
            let expr1_type = check_expr_types(tr, st, handler, exprid1)?;
            let expr2_type = check_expr_types(tr, st, handler, exprid2)?;
            if expr1_type.is_equivalent(&expr2_type) {
                Ok(())
            } else {
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
                check_stmt_types(tr, st, handler, stmtid)?;
            }
            Ok(())
        }
    }
}

/// Typechecks every function contained in the argument `Vec`
/// of `(Transaction, SymbolTable)` pairs
pub fn type_check(
    trs: &Vec<(Transaction, SymbolTable)>,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    for (tr, st) in trs {
        for expr_id in tr.expr_ids() {
            check_expr_types(tr, st, handler, &expr_id)?;
        }

        for stmt_id in tr.stmt_ids() {
            check_stmt_types(tr, st, handler, &stmt_id)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::parser::parse_file;
    use baa::BitVecValue;
    use insta::Settings;
    use strip_ansi_escapes::strip_str;

    use super::*;

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
            Ok(trs) => {
                let _ = type_check(&trs, &mut handler);
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

    // Specific Tests
    #[test]
    fn function_argument_test() {
        let mut handler = DiagnosticHandler::default();
        let mut symbols = SymbolTable::default();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(1));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(1));
        let c: SymbolId = symbols.add_without_parent("c".to_string(), Type::BitVec(1));
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(1));
        assert_eq!(symbols["s"], symbols[s]);
        let input =
            std::fs::read_to_string("tests/misc/func_arg_invalid.prot").expect("failed to load");
        let fileid = handler.add_file("func_arg_invalid.prot".to_string(), input);
        let mut tr = Transaction::new("func_arg_invalid".to_string());
        tr.args = vec![
            Arg::new(a, Dir::In),
            Arg::new(b, Dir::In),
            Arg::new(s, Dir::Out),
        ];

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
        let _ = type_check(&vec![(tr, symbols)], &mut handler);
    }
}
