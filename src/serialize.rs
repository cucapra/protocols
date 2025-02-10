// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{any::Any, fmt::format, io::Write};

use baa::BitVecOps;

use crate::{diagnostic::*, ir::*};

pub fn serialize_to_string(tr: &Transaction, st: &SymbolTable) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, tr, st)?;
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

pub fn serialize_expr(tr: &Transaction, st: &SymbolTable, expr_id: &ExprId) -> String {
    match &tr[expr_id] {
        Expr::Const(val) => val.to_i64().unwrap().to_string(),
        Expr::Sym(symid) => st[symid].full_name(st),
        Expr::DontCare => "X".to_owned(),
        Expr::Unary(UnaryOp::Not, not_exprid) => {
            "!(".to_owned() + &serialize_expr(tr, st, not_exprid) + ")"
        }
        Expr::Binary(BinOp::And, lhs, rhs) => {
            serialize_expr(tr, st, lhs) + " && " + &serialize_expr(tr, st, rhs)
        }
        Expr::Binary(BinOp::Equal, lhs, rhs) => {
            serialize_expr(tr, st, lhs) + " == " + &serialize_expr(tr, st, rhs)
        }
    }
}

fn build_statements(
    out: &mut impl Write,
    tr: &Transaction,
    st: &SymbolTable,
    stmtid: &StmtId,
    index: usize,
) -> std::io::Result<()> {
    match &tr[stmtid] {
        Stmt::Skip => writeln!(out, "{}skip()", "  ".repeat(index))?,
        Stmt::Block(stmts) => {
            for stmt_id in stmts {
                build_statements(out, tr, st, stmt_id, index)?;
            }
        }
        Stmt::Assign(lhs, rhs) => writeln!(
            out,
            "{}{} := {};",
            "  ".repeat(index),
            st[lhs].full_name(st),
            serialize_expr(tr, st, rhs)
        )?,
        Stmt::Step(expr_id) => writeln!(
            out,
            "{}step({});",
            "  ".repeat(index),
            serialize_expr(tr, st, expr_id)
        )?,
        Stmt::Fork => writeln!(out, "{}fork();", "  ".repeat(index))?,
        Stmt::While(cond, bodyid) => {
            writeln!(
                out,
                "{}while {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, cond)
            )?;
            build_statements(out, tr, st, bodyid, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            writeln!(
                out,
                "{}if {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, cond)
            )?;
            build_statements(out, tr, st, ifbody, index + 1)?;
            writeln!(out, "{}}} else {{", "  ".repeat(index))?;
            build_statements(out, tr, st, elsebody, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
        Stmt::AssertEq(exprid1, exprid2) => {
            writeln!(
                out,
                "{}assert_eq({}, {});",
                "  ".repeat(index),
                serialize_expr(tr, st, exprid1),
                serialize_expr(tr, st, exprid2)
            )?;
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

pub fn serialize(out: &mut impl Write, tr: &Transaction, st: &SymbolTable) -> std::io::Result<()> {
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

    build_statements(out, tr, st, &tr.body, 1)?;

    writeln!(out, "}}")?;

    Ok(())
}

#[cfg(test)]
pub mod tests {
    use insta::Settings;
    use std::path::Path;
    use crate::parser::parse_file;

    use baa::BitVecValue;

    use super::*;

    #[test]
    fn test_add_transaction() {
        let mut handler = DiagnosticHandler::new();
        let (add, symbols) = parse_file("tests/add_struct.prot", &mut handler);

        let content = serialize_to_string(&add, &symbols).unwrap();

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(content);
        });
    }

    #[test]
    fn test_calyx_go_done_transaction() {
        let mut handler = DiagnosticHandler::new();
        let (calyx_go_done, symbols) = parse_file("tests/calyx_go_done_struct.prot", &mut handler);

        let content = serialize_to_string(&calyx_go_done, &symbols).unwrap();
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(content);
        });
    }

    #[test]
    fn serialize_easycond_transaction() {
        // Manually create the expected result of parsing `easycond.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
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
        let one_expr = easycond.e(Expr::Const(BitVecValue::from_i64(1, 2)));
        let cond_expr = easycond.e(Expr::Binary(BinOp::Equal, dut_a_expr, one_expr));

        // 4) create statements
        let if_body = vec![easycond.s(Stmt::Step(one_expr))];
        let ifbody = easycond.s(Stmt::Block(if_body));

        let else_body = vec![easycond.s(Stmt::Fork)];
        let elsebody = easycond.s(Stmt::Block(else_body));

        let body = vec![
            easycond.s(Stmt::Assign(dut_a, a_expr)),
            easycond.s(Stmt::IfElse(cond_expr, ifbody, elsebody)),
            easycond.s(Stmt::Assign(b, one_expr)),
        ];
        easycond.body = easycond.s(Stmt::Block(body));
        println!("{}", serialize_to_string(&easycond, &symbols).unwrap());
    }
}
