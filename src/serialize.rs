// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{any::Any, fmt::format, io::Write};

use baa::BitVecOps;

use crate::{diagnostic::*, ir::*};

pub fn serialize_to_string(trs: Vec<(SymbolTable, Transaction)>) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, trs)?;
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
        Expr::Slice(expr, idx1, idx2) => {
            if *idx2 == *idx1 {
                serialize_expr(tr, st, expr) + "[" + idx1.to_string().as_str() + "]"
            } else {
                serialize_expr(tr, st, expr)
                    + "["
                    + idx1.to_string().as_str()
                    + ":"
                    + idx2.to_string().as_str()
                    + "]"
            }
        }
    }
}

pub fn build_statements(
    out: &mut impl Write,
    tr: &Transaction,
    st: &SymbolTable,
    stmtid: &StmtId,
    index: usize,
) -> std::io::Result<()> {
    match &tr[stmtid] {
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

pub fn serialize(
    out: &mut impl Write,
    trs: Vec<(SymbolTable, Transaction)>,
) -> std::io::Result<()> {
    let (st, _) = &trs[0];

    if st.struct_ids().len() > 0 {
        serialize_structs(out, &st, st.struct_ids())?;
    }

    for (st, tr) in trs {
        write!(out, "fn {}", tr.name)?;

        for (ii, tpe_arg) in tr.type_args.iter().enumerate() {
            let last_index = ii == tr.type_args.len() - 1;

            if ii == 0 {
                write!(out, "<")?;
            }

            let strct_type = serialize_type(&st, st[tpe_arg].tpe());

            if last_index {
                write!(out, "{}: {}>", st[tpe_arg].name(), strct_type)?;
            } else {
                write!(out, "{}: {}, ", st[tpe_arg].name(), strct_type)?;
            }
        }

        write!(out, "(")?;

        if tr.args.len() == 0 {
            write!(out, ") {{\n")?;
        } else {
            for (ii, arg) in tr.args.iter().enumerate() {
                let last_index = ii == tr.args.len() - 1;

                if last_index {
                    write!(
                        out,
                        "{} {}: {}) {{\n",
                        serialize_dir(arg.dir()),
                        st[arg].name(),
                        serialize_type(&st, st[arg].tpe())
                    )?;
                } else {
                    write!(
                        out,
                        "{} {}: {}, ",
                        serialize_dir(arg.dir()),
                        st[arg].name(),
                        serialize_type(&st, st[arg].tpe())
                    )?;
                }
            }
        }

        build_statements(out, &tr, &st, &tr.body, 1)?;

        writeln!(out, "}}\n")?;
    }

    Ok(())
}

#[cfg(test)]
pub mod tests {
    use crate::parser::parse_file;
    use insta::Settings;
    use std::path::Path;

    use baa::BitVecValue;
    use strip_ansi_escapes::strip_str;

    use super::*;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    fn test_helper(filename: &str, snap_name: &str) {
        let mut handler = DiagnosticHandler::new();
        let result = parse_file(filename, &mut handler);

        let content = match result {
            Ok(trs) => serialize_to_string(trs).unwrap(),
            Err(_) => strip_str(handler.error_string()),
        };
        println!("{}", content);
        snap(snap_name, content);
    }

    #[test]
    fn test_add_transaction() {
        test_helper("tests/add_struct.prot", "add_struct");
    }

    #[test]
    fn test_calyx_go_done_transaction() {
        test_helper("tests/calyx_go_done_struct.prot", "calyx_go_done_struct");
    }

    #[test]
    fn test_invalid_lex_prot() {
        test_helper("tests/invalid_lex.prot", "invalid_lex");
    }

    #[test]
    fn test_aes128_prot() {
        test_helper("tests/aes128.prot", "aes128");
    }

    #[test]
    fn test_aes128_round_prot() {
        test_helper("tests/aes128_round.prot", "aes128_round");
    }

    #[test]
    fn test_aes128_expand_key_prot() {
        test_helper("tests/aes128_expand_key.prot", "aes128_expand_key");
    }

    #[test]
    fn test_mul_invalid_prot() {
        test_helper("tests/mul_invalid.prot", "mul_invalid");
    }

    #[test]
    fn test_mul_prot() {
        test_helper("tests/mul.prot", "mul");
    }

    #[test]
    fn test_mul_ignore_prot() {
        test_helper("tests/mul_ignore.prot", "mul_ignore");
    }

    #[test]
    fn test_cond_prot() {
        test_helper("tests/cond.prot", "cond");
    }

    #[test]
    fn test_parse_serv_register_file_prot() {
        test_helper("tests/serv/register_file.prot", "parse_serv_register_file");
    }

    #[test]
    fn test_illegal_fork_prot() {
        test_helper("tests/illegal_fork.prot", "illegal_fork_prot");
    }

    #[test]
    fn test_invalid_step_arg() {
        test_helper("tests/invalid_step_arg.prot", "invalid_step_arg");
    }

    #[test]
    fn test_func_arg_invalid_prot() {
        test_helper("tests/func_arg_invalid.prot", "func_arg_invalid_prot");
    }

    #[test]
    fn test_simple_if_transaction() {
        test_helper("tests/simple_if.prot", "simple_if");
    }

    #[test]
    fn test_simple_while_transaction() {
        test_helper("tests/simple_while.prot", "simple_while");
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
            "UnaryOp".to_string(),
            vec![
                Field::new("a".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("b".to_string(), Dir::In, Type::BitVec(32)),
            ],
        );
        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_a = symbols.add_with_parent("a".to_string(), dut);
        assert_eq!(symbols["dut.a"], symbols[dut_a]);

        // 2) create transaction
        let mut easycond = Transaction::new("easycond".to_string());
        easycond.args = vec![Arg::new(a, Dir::In), Arg::new(b, Dir::Out)];
        easycond.type_args = vec![dut];

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
        println!(
            "{}",
            serialize_to_string(vec![(symbols, easycond)]).unwrap()
        );
    }
}
