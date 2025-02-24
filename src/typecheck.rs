// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use crate::parser;
use crate::{diagnostic::*, ir::*, serialize::*};

fn check_expr_types(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    expr_id: &ExprId,
) -> Result<Type, String> {
    match &tr[expr_id] {
        Expr::Const(_) => Ok(Type::BitVec(1)),
        Expr::Sym(symid) => Ok(st[symid].tpe()),
        Expr::DontCare => Ok(Type::Unknown),
        // FIXME: is this the correct typechecking logic?
        Expr::Slice(sym_expr, _, _) => check_expr_types(tr, st, handler, sym_expr),
        Expr::Unary(UnaryOp::Not, not_exprid) => {
            let inner_type = check_expr_types(tr, st, handler, not_exprid)?;
            if let Type::BitVec(_) = inner_type {
                Ok(inner_type)
            } else {
                handler.emit_diagnostic_expr(
                    tr,
                    expr_id,
                    &format!("Invalid type for 'Not' expression {:?}", inner_type).to_string(),
                    Level::Error,
                );
                Ok(inner_type)
            }
        }
        Expr::Binary(BinOp::And, lhs, rhs) | Expr::Binary(BinOp::Equal, lhs, rhs) => {
            let lhs_type = check_expr_types(tr, st, handler, lhs)?;
            let rhs_type = check_expr_types(tr, st, handler, rhs)?;
            if lhs_type.is_equivalent(&rhs_type) {
                Ok(lhs_type)
            } else {
                handler.emit_diagnostic_expr(
                    tr,
                    expr_id,
                    &format!(
                        "Type mismatch in binary operation: {:?} and {:?}",
                        lhs_type, rhs_type
                    ),
                    Level::Error,
                );
                Ok(lhs_type)
            }
        }
    }
}

fn check_stmt_types(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    stmt_id: &StmtId,
) -> Result<(), String> {
    match &tr[stmt_id] {
        Stmt::Skip | Stmt::Fork => Ok(()),
        Stmt::Step(exprid) => {
            let expr_type = check_expr_types(tr, st, handler, exprid)?;
            if let Type::BitVec(_) = expr_type {
                Ok(())
            } else {
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!("Invalid type for [step] statement: {:?}", expr_type),
                    Level::Error,
                );
                Ok(())
            }
        }
        Stmt::Assign(lhs, rhs) => {
            // Function argument cannot be assigned
            if tr.args.iter().any(|arg| arg.symbol() == *lhs) {
                handler.emit_diagnostic_stmt(tr, stmt_id, "Cannot assign to function argument. Try using assert_eq if you want to check the value of a transaction output.", Level::Error);
            }
            // DUT output cannot be assigned
            if let Some(parent) = st[lhs].parent() {
                if let Type::Struct(structid) = st[parent].tpe() {
                    let fields = st[structid].pins();
                    if fields
                        .iter()
                        .find(|field| field.dir() == Dir::Out && field.name() == st[lhs].name())
                        .is_some()
                    {
                        handler.emit_diagnostic_stmt(
                            tr,
                            stmt_id,
                            &format!(
                                "{} is an output and thus cannot be assigned.",
                                st[lhs].full_name(st)
                            ),
                            Level::Error,
                        );
                    }
                }
            }
            let lhs_type = st[lhs].tpe();
            let mut rhs_type = check_expr_types(tr, st, handler, rhs)?;
            if rhs_type == Type::Unknown {
                rhs_type = lhs_type.clone();
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!(
                        "Inferred RHS type as {:?} from LHS type {:?}.",
                        rhs_type, lhs_type
                    ),
                    Level::Warning,
                );
            }
            if lhs_type.is_equivalent(&rhs_type) {
                Ok(())
            } else {
                let expr_name = serialize_expr(tr, st, rhs);
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!(
                        "Type mismatch in assignment: {} : {:?} and {} : {:?}.",
                        st[lhs].full_name(st),
                        lhs_type,
                        expr_name,
                        rhs_type
                    ),
                    Level::Error,
                );
                Ok(())
            }
        }
        Stmt::While(cond, bodyid) => {
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            if let Type::BitVec(1) = cond_type {
                check_stmt_types(tr, st, handler, bodyid)
            } else {
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!("Invalid type for [while] condition: {:?}", cond_type),
                    Level::Error,
                );
                Ok(())
            }
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            if let Type::BitVec(_) = cond_type {
                check_stmt_types(tr, st, handler, ifbody)?;
                check_stmt_types(tr, st, handler, elsebody)?;
                Ok(())
            } else {
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!("Type mistmatch in If/Else condition: {:?}", cond_type),
                    Level::Error,
                );
                Ok(())
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
                handler.emit_diagnostic_stmt(
                    tr,
                    stmt_id,
                    &format!(
                        "Type mismatch in assert_eq: {} : {:?} and {} : {:?}.",
                        expr1_name, expr1_type, expr2_name, expr2_type,
                    ),
                    Level::Error,
                );
                Ok(())
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

pub fn type_check(trs: Vec<(SymbolTable, Transaction)>, handler: &mut DiagnosticHandler) {
    for (st, tr) in trs {
        for expr_id in tr.expr_ids() {
            let _ = check_expr_types(&tr, &st, handler, &expr_id);
        }

        for stmt_id in tr.stmt_ids() {
            let _ = check_stmt_types(&tr, &st, handler, &stmt_id);
        }
    }
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

    #[test]
    fn test_add_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parse_file("tests/add_struct.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);

        let content = strip_str(handler.error_string());

        snap("add_struct", content);
    }

    #[test]
    fn test_invalid_step_arg_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/invalid_step_arg.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);

        let content = strip_str(handler.error_string());

        snap("invalid_step_arg", content);
    }

    #[test]
    fn typecheck_aes128_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/aes128.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);
        let content = strip_str(handler.error_string());

        snap("aes128", content);
    }

    #[test]
    fn typecheck_aes128_expand_key_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/aes128_expand_key.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);
        let content = strip_str(handler.error_string());

        snap("aes128_expand_key", content);
    }

    #[test]
    fn typecheck_aes128_round_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/aes128_round.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);
        let content = strip_str(handler.error_string());

        snap("aes128_round", content);
    }

    #[test]
    fn typecheck_mul_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/mul.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);
        let content = strip_str(handler.error_string());

        snap("mul", content);
    }

    #[test]
    fn typecheck_cond_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parser::parse_file("tests/cond.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);
        let content = strip_str(handler.error_string());

        snap("cond", content);
    }

    #[test]
    fn test_calyx_go_done_transaction() {
        let mut handler = DiagnosticHandler::new();
        let trs = parse_file("tests/calyx_go_done_struct.prot", &mut handler);
        type_check(trs.unwrap(), &mut handler);

        let content = strip_str(handler.error_string());

        snap("calyx_go_done_struct", content);
    }

    // Specific Tests
    #[test]
    fn function_argument_test() {
        let mut handler = DiagnosticHandler::new();
        let mut symbols = SymbolTable::default();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(1));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(1));
        let c: SymbolId = symbols.add_without_parent("c".to_string(), Type::BitVec(1));
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(1));
        assert_eq!(symbols["s"], symbols[s]);
        let input = std::fs::read_to_string("tests/func_arg_invalid.prot").expect("failed to load");
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
        let step = tr.s(Stmt::Step(one_expr));
        tr.add_stmt_loc(step, 90, 97, fileid);
        let s_assign = tr.s(Stmt::Assign(s, zero_expr));
        tr.add_stmt_loc(s_assign, 101, 108, fileid);
        let body = vec![a_assign, fork, c_assign, step, s_assign];
        tr.body = tr.s(Stmt::Block(body));
        type_check(vec![(symbols, tr)], &mut handler);
    }
}
