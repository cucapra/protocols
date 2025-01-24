// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

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
        Expr::Not(not_exprid) => {
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
        Expr::And(lhs, rhs) | Expr::Equal(lhs, rhs) => {
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
        Stmt::Skip | Stmt::Step | Stmt::Fork => Ok(()),
        Stmt::Assign(lhs, rhs) => {
            let lhs_type = st[lhs].tpe();
            let rhs_type = check_expr_types(tr, st, handler, rhs)?;
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
        Stmt::Block(stmts) => {
            for stmtid in stmts {
                check_stmt_types(tr, st, handler, stmtid)?;
            }
            Ok(())
        }
    }
}

pub fn type_check(tr: &Transaction, st: &SymbolTable, handler: &mut DiagnosticHandler) {
    for expr_id in tr.expr_ids() {
        let _ = check_expr_types(tr, st, handler, &expr_id);
    }

    for stmt_id in tr.stmt_ids() {
        let _ = check_stmt_types(tr, st, handler, &stmt_id);
    }
}

mod tests {
    use baa::BitVecValue;

    use super::*;

    #[test]
    fn serialize_calyx_go_down_transaction() {
        // Manually create the expected result of parsing `calyx_go_down`.
        // Note that the order in which things are created will be different in the parser.

        // TODO: create this into function that factors our the code to put src code into IR

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler: DiagnosticHandler = DiagnosticHandler::new();

        let ii = symbols.add_without_parent("ii".to_string(), Type::BitVec(32));
        let oo = symbols.add_without_parent("oo".to_string(), Type::BitVec(32));
        assert_eq!(symbols["oo"], symbols[oo]);

        // declare Calyx struct
        let dut_struct = symbols.add_struct(
            "Calyx".to_string(),
            vec![
                Field::new("ii".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("go".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("done".to_string(), Dir::Out, Type::BitVec(1)),
                Field::new("oo".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_ii = symbols.add_with_parent("ii".to_string(), dut);
        let dut_go = symbols.add_with_parent("go".to_string(), dut);
        let dut_done = symbols.add_with_parent("done".to_string(), dut);
        let dut_oo = symbols.add_with_parent("oo".to_string(), dut);
        assert_eq!(symbols["dut.oo"], symbols[dut_oo]);
        assert_eq!(symbols["oo"], symbols[oo]);

        // create fileid and read file
        let input =
            std::fs::read_to_string("tests/calyx_go_done_struct.prot").expect("failed to load");
        let calyx_fileid = handler.add_file("calyx_go_done.prot".to_string(), input);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];
        calyx_go_done.type_args = vec![dut];

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        calyx_go_done.add_expr_loc(ii_expr, 153, 155, calyx_fileid);
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        calyx_go_done.add_expr_loc(dut_oo_expr, 260, 266, calyx_fileid);
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        calyx_go_done.add_expr_loc(one_expr, 170, 171, calyx_fileid);
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        calyx_go_done.add_expr_loc(zero_expr, 232, 233, calyx_fileid);
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        calyx_go_done.add_expr_loc(dut_done_expr, 184, 192, calyx_fileid);
        let cond_expr = calyx_go_done.e(Expr::Equal(dut_done_expr, one_expr));
        calyx_go_done.add_expr_loc(cond_expr, 183, 198, calyx_fileid);
        let not_expr = calyx_go_done.e(Expr::Not(cond_expr));
        calyx_go_done.add_expr_loc(not_expr, 182, 198, calyx_fileid);

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let dut_ii_assign = calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr));
        calyx_go_done.add_stmt_loc(dut_ii_assign, 143, 157, calyx_fileid);
        let dut_go_assign = calyx_go_done.s(Stmt::Assign(dut_go, one_expr));
        calyx_go_done.add_stmt_loc(dut_go_assign, 160, 172, calyx_fileid);
        let dut_while = calyx_go_done.s(Stmt::While(not_expr, wbody));
        calyx_go_done.add_stmt_loc(dut_while, 175, 219, calyx_fileid);
        let dut_go_reassign = calyx_go_done.s(Stmt::Assign(dut_go, zero_expr));
        calyx_go_done.add_stmt_loc(dut_go_reassign, 222, 234, calyx_fileid);
        let dut_ii_dontcare = calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care()));
        calyx_go_done.add_stmt_loc(dut_ii_dontcare, 238, 250, calyx_fileid);
        let oo_assign = calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr));
        calyx_go_done.add_stmt_loc(oo_assign, 254, 268, calyx_fileid);
        let body = vec![
            dut_ii_assign,
            dut_go_assign,
            dut_while,
            dut_go_reassign,
            dut_ii_dontcare,
            oo_assign,
        ];
        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));
        type_check(&calyx_go_done, &symbols, &mut handler);
    }
}
