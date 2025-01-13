// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{any::Any, fmt::format, io::Write};

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
    expr_id: &ExprId,
) -> String {
    match &tr[expr_id] {
        Expr::Const(val) => val.to_bit_str(),
        Expr::Sym(symid) => st[symid].full_name(st),
        Expr::DontCare => "X".to_owned(),
        Expr::Not(not_exprid) => {
            "!(".to_owned() + &serialize_expr(tr, st, handler, not_exprid) + ")"
        }
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
                let expr_name = serialize_expr(tr, st, handler, rhs);
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
    use baa::BitVecValue;

    use super::*;

    #[test]
    fn serialize_add_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler = DiagnosticHandler::new();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(32));
        let s = symbols.add_without_parent("s".to_string(), Type::BitVec(32));
        assert_eq!(symbols["s"], symbols[s]);

        // declare Adder struct
        let add_struct = symbols.add_struct(
            "Adder".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("s".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        let dut = symbols.add_without_parent("DUT".to_string(), Type::Struct(add_struct));

        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        let dut_b = symbols.add_with_parent("b".to_string(), dut);
        let dut_s = symbols.add_with_parent("s".to_string(), dut);
        assert_eq!(symbols["DUT.s"], symbols[dut_s]);
        assert_eq!(symbols["s"], symbols[s]);

        // 2) create transaction
        let mut add = Transaction::new("add".to_string());
        add.args = vec![
            Arg::new(a, Dir::In),
            Arg::new(b, Dir::In),
            Arg::new(s, Dir::Out),
        ];
        add.type_args = vec![dut];

        // 3) create expressions
        let a_expr = add.e(Expr::Sym(a));
        let b_expr = add.e(Expr::Sym(b));
        let dut_s_expr = add.e(Expr::Sym(dut_s));

        // 4) create statements
        let body = vec![
            add.s(Stmt::Assign(dut_a, a_expr)),
            add.s(Stmt::Assign(dut_b, b_expr)),
            add.s(Stmt::Step),
            add.s(Stmt::Fork),
            add.s(Stmt::Assign(dut_a, add.expr_dont_care())),
            add.s(Stmt::Assign(dut_b, add.expr_dont_care())),
            add.s(Stmt::Assign(s, dut_s_expr)),
        ];
        add.body = add.s(Stmt::Block(body));

        println!(
            "{}",
            serialize_to_string(&add, &symbols, &mut handler).unwrap()
        );
    }

    #[test]
    fn serialize_calyx_go_down_transaction() {
        // Manually create the expected result of parsing `calyx_go_down`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler = DiagnosticHandler::new();
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
        let input = std::fs::read_to_string("tests/calyx_go_done.prot").expect("failed to load");
        let calyx_fileid = handler.add_file("calyx_go_done.prot".to_string(), input);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];
        calyx_go_done.type_args = vec![dut];

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        calyx_go_done.add_expr_md(ii_expr, 153, 155, calyx_fileid);
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        calyx_go_done.add_expr_md(dut_oo_expr, 260, 266, calyx_fileid);
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        calyx_go_done.add_expr_md(one_expr, 170, 171, calyx_fileid);
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        calyx_go_done.add_expr_md(zero_expr, 232, 233, calyx_fileid);
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        calyx_go_done.add_expr_md(dut_done_expr, 184, 192, calyx_fileid);
        let cond_expr = calyx_go_done.e(Expr::Equal(dut_done_expr, one_expr));
        calyx_go_done.add_expr_md(cond_expr, 183, 198, calyx_fileid);
        let not_expr = calyx_go_done.e(Expr::Not(cond_expr));
        calyx_go_done.add_expr_md(not_expr, 182, 198, calyx_fileid);

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let dut_ii_assign = calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr));
        calyx_go_done.add_stmt_md(dut_ii_assign, 143, 157, calyx_fileid);
        let dut_go_assign = calyx_go_done.s(Stmt::Assign(dut_go, one_expr));
        calyx_go_done.add_stmt_md(dut_go_assign, 160, 172, calyx_fileid);
        let dut_while = calyx_go_done.s(Stmt::While(not_expr, wbody));
        calyx_go_done.add_stmt_md(dut_while, 175, 219, calyx_fileid);
        let dut_go_reassign = calyx_go_done.s(Stmt::Assign(dut_go, zero_expr));
        calyx_go_done.add_stmt_md(dut_go_reassign, 222, 234, calyx_fileid);
        let dut_ii_dontcare = calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care()));
        calyx_go_done.add_stmt_md(dut_ii_dontcare, 238, 250, calyx_fileid);
        let oo_assign = calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr));
        calyx_go_done.add_stmt_md(oo_assign, 254, 268, calyx_fileid);
        let body = vec![
            dut_ii_assign,
            dut_go_assign,
            dut_while,
            dut_go_reassign,
            dut_ii_dontcare,
            oo_assign,
        ];
        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));
        println!(
            "{}",
            serialize_to_string(&calyx_go_done, &symbols, &mut handler).unwrap()
        );
    }

    #[test]
    fn serialize_easycond_transaction() {
        // Manually create the expected result of parsing `easycond.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler = DiagnosticHandler::new();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));
        let b: SymbolId = symbols.add_without_parent("b".to_string(), Type::BitVec(32));
        assert_eq!(symbols["b"], symbols[b]);

        // declare DUT struct (TODO: Fix struct)
        let dut_struct = symbols.add_struct(
            "Adder".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("s".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );
        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        assert_eq!(symbols["dut.a"], symbols[dut_a]);

        // 2) create transaction
        let mut easycond = Transaction::new("easycond".to_string());
        easycond.args = vec![Arg::new(a, Dir::In), Arg::new(b, Dir::Out)];

        // 3) create expressions
        let a_expr = easycond.e(Expr::Sym(a));
        let dut_a_expr = easycond.e(Expr::Sym(dut_a));
        let one_expr = easycond.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let cond_expr = easycond.e(Expr::Equal(dut_a_expr, one_expr));

        // 4) create statements
        let if_body = vec![easycond.s(Stmt::Step)];
        let ifbody = easycond.s(Stmt::Block(if_body));

        let else_body = vec![easycond.s(Stmt::Fork)];
        let elsebody = easycond.s(Stmt::Block(else_body));

        let body = vec![
            easycond.s(Stmt::Assign(dut_a, a_expr)),
            easycond.s(Stmt::IfElse(cond_expr, ifbody, elsebody)),
            easycond.s(Stmt::Assign(b, one_expr)),
        ];
        easycond.body = easycond.s(Stmt::Block(body));
        println!(
            "{}",
            serialize_to_string(&easycond, &symbols, &mut handler).unwrap()
        );
    }
}
