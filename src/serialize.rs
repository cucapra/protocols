// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{any::Any, io::Write, process::exit};

use baa::BitVecOps;

use crate::{diagnostic::*, ir::*};

fn serialize_to_string(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, tr, st, handler)?;
    let out = String::from_utf8(out).unwrap();
    Ok(out)
}

fn serialize_type(st: &SymbolTable, tpe: Type) -> String {
    match tpe {
        Type::BitVec(t) => "u".to_owned() + &t.to_string(),
        Type::Struct(structid) => st[structid].name().to_owned(),
        Type::Unknown => "unknown".to_string(),
    }
}

fn serialize_dir(dir: Dir) -> String {
    match dir {
        Dir::In => "in".to_string(),
        Dir::Out => "out".to_string(),
    }
}

fn serialize_expr(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    exprid: &ExprId,
) -> String {
    match &tr[exprid] {
        Expr::Const(val) => val.to_bit_str(),
        Expr::Sym(symid) => st[symid].full_name(st),
        Expr::DontCare => "X".to_owned(),
        Expr::Not(exprid) => "!(".to_owned() + &serialize_expr(tr, st, handler, exprid) + ")",
        Expr::And(lhs, rhs) => {
            serialize_expr(tr, st, handler, lhs) + " && " + &serialize_expr(tr, st, handler, rhs)
        }
        Expr::Equal(lhs, rhs) => {
            serialize_expr(tr, st, handler, lhs) + " == " + &serialize_expr(tr, st, handler, rhs)
        }
    }
}

fn build_statements(
    out: &mut impl Write,
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    stmtid: &StmtId,
    index: usize,
) -> std::io::Result<()> {
    match &tr[stmtid] {
        Stmt::Skip => writeln!(out, "{}skip()", "  ".repeat(index))?,
        Stmt::Block(stmts) => {
            for stmt_id in stmts {
                build_statements(out, tr, st, handler, stmt_id, index)?;
            }
        }
        Stmt::Assign(lhs, rhs) => writeln!(
            out,
            "{}{} := {};",
            "  ".repeat(index),
            st[lhs].full_name(st),
            serialize_expr(tr, st, handler, rhs)
        )?,
        Stmt::Step => writeln!(out, "{}step();", "  ".repeat(index))?,
        Stmt::Fork => writeln!(out, "{}fork();", "  ".repeat(index))?,
        Stmt::While(cond, bodyid) => {
            writeln!(
                out,
                "{}while {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, handler, cond)
            )?;
            build_statements(out, tr, st, handler, bodyid, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            writeln!(
                out,
                "{}if {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, handler, cond)
            )?;
            build_statements(out, tr, st, handler, ifbody, index + 1)?;
            writeln!(out, "{}}} else {{", "  ".repeat(index))?;
            build_statements(out, tr, st, handler, elsebody, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
    }

    Ok(())
}

pub fn serialize_structs(
    out: &mut impl Write,
    st: &SymbolTable,
    strct_ids: Vec<StructId>,
) -> std::io::Result<()> {
    for strct_id in strct_ids {
        writeln!(out, "struct {} {{", st[strct_id].name())?;

        for field in st[strct_id].pins() {
            writeln!(
                out,
                "{}{} {}: {},",
                "  ".repeat(1),
                serialize_dir(field.dir()),
                field.name(),
                serialize_type(st, field.tpe())
            )?;
        }
        writeln!(out, "}}\n")?;
    }

    Ok(())
}

pub fn serialize(
    out: &mut impl Write,
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> std::io::Result<()> {
    type_check(tr, st, handler);

    if st.struct_ids().len() > 0 {
        serialize_structs(out, st, st.struct_ids())?;
    }

    write!(out, "fn {}", tr.name)?;

    for (ii, tpe_arg) in tr.type_args.iter().enumerate() {
        let last_index = ii == tr.type_args.len() - 1;

        if ii == 0 {
            write!(out, "<")?;
        }

        let strct_type = serialize_type(st, st[tpe_arg].tpe());

        if last_index {
            write!(out, "{}: {}>", st[tpe_arg].name(), strct_type)?;
        } else {
            write!(out, "{}: {}, ", st[tpe_arg].name(), strct_type)?;
        }
    }

    write!(out, "(")?;

    for (ii, arg) in tr.args.iter().enumerate() {
        let last_index = ii == tr.args.len() - 1;

        if last_index {
            write!(
                out,
                "{} {}: {}) {{\n",
                serialize_dir(arg.dir()),
                st[arg].name(),
                serialize_type(st, st[arg].tpe())
            )?;
        } else {
            write!(
                out,
                "{} {}: {}, ",
                serialize_dir(arg.dir()),
                st[arg].name(),
                serialize_type(st, st[arg].tpe())
            )?;
        }
    }

    build_statements(out, tr, st, handler, &tr.body, 1)?;

    writeln!(out, "}}")?;

    Ok(())
}

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
                // TODO: create meta data (secondary map) and send error
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
                // TODO: create meta data (secondary map) and send error
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
                panic!(
                    "Type mismatch in assignment: {} : {:?} (lhs) and {} : {:?} (rhs).",
                    st[lhs].full_name(st),
                    lhs_type,
                    serialize_expr(tr, st, handler, rhs),
                    rhs_type
                )
            }
        }
        Stmt::While(cond, bodyid) => {
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            if let Type::BitVec(1) = cond_type {
                check_stmt_types(tr, st, handler, bodyid)
            } else {
                panic!("Invalid type for [while] condition: {:?}", cond_type)
            }
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            let cond_type = check_expr_types(tr, st, handler, cond)?;
            if let Type::BitVec(_) = cond_type {
                check_stmt_types(tr, st, handler, ifbody)?;
                check_stmt_types(tr, st, handler, elsebody)?;
                Ok(())
            } else {
                panic!("Type mistmatch in If/Else condition: {:?}", cond_type)
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
    for exprid in tr.expr_ids() {
        check_expr_types(tr, st, handler, &exprid);
    }

    for stmt_id in tr.stmt_ids() {
        check_stmt_types(tr, st, handler, &stmt_id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::tests::*;
    use baa::BitVecValue;

    #[test]
    fn serialize_add_transaction() {
        let (mut handler, symbols, add) = build_add_transaction();
        println!(
            "{}",
            serialize_to_string(&add, &symbols, &mut handler).unwrap()
        );
    }

    #[test]
    fn serialize_calyx_go_done_transaction() {
        let (mut handler, symbols, calyx_go_done) = build_calyx_go_done_transaction();
        println!(
            "{}",
            serialize_to_string(&calyx_go_done, &symbols, &mut handler).unwrap()
        );
    }

    #[test]
    fn serialize_easycond_transaction() {
        let (mut handler, symbols, easycond) = build_easycond_transaction();
        println!(
            "{}",
            serialize_to_string(&easycond, &symbols, &mut handler).unwrap()
        );
    }
}
