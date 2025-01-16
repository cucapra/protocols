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

#[cfg(test)]
mod tests {
    use crate::serialize::tests::{create_add_transaction, create_calyx_go_down_transaction};

    use super::*;

    #[test]
    fn typecheck_add_transaction() {
        let mut handler = DiagnosticHandler::new();
        let (add, symbols) = create_add_transaction(&mut handler);
        type_check(&add, &symbols, &mut handler);
    }

    #[test]
    fn typecheck_calyx_go_down_transaction() {
        let mut handler = DiagnosticHandler::new();
        let (calyx_go_done, symbols) = create_calyx_go_down_transaction(&mut handler);
        type_check(&calyx_go_done, &symbols, &mut handler);
    }
}
