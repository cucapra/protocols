use std::{any::Any, io::Write};

use baa::BitVecOps;

use crate::ir::*;

pub fn serialize_to_string(tr: &Transaction, st: &SymbolTable) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, tr, st)?;
    let out = String::from_utf8(out).unwrap();
    Ok(out)
}

// TODO need to fix for other types
pub fn serialize_type(tpe: Type) -> String {
    match tpe {
        Type::BitVec(t) => "u".to_owned() + &t.to_string(),
        Type::Struct(_) => todo!(),
        Type::Unknown => "unknown".to_string(),
    }
}

pub fn serialize_dir(el: &Arg) -> String {
    match el.dir() {
        Dir::In => "in".to_string(),
        Dir::Out => "out".to_string(),
    }
}

pub fn serialize_expr(tr: &Transaction, st: &SymbolTable, expr: &Expr) -> String {
    match expr {
        Expr::Const(val) => val.to_bit_str(),
        Expr::Sym(symid) => st[symid].full_name(st),
        Expr::DontCare => "X".to_owned(),
        Expr::Not(exprid) => "!(".to_owned() + &serialize_expr(tr, st, &tr[exprid]) + ")",
        Expr::And(lhs, rhs) => {
            serialize_expr(tr, st, &tr[lhs]) + " && " + &serialize_expr(tr, st, &tr[rhs])
        }
        Expr::Equal(lhs, rhs) => {
            serialize_expr(tr, st, &tr[lhs]) + " == " + &serialize_expr(tr, st, &tr[rhs])
        }
    }
}

pub fn build_statements(
    out: &mut impl Write,
    tr: &Transaction,
    st: &SymbolTable,
    stmtid: StmtId,
    index: usize,
) -> std::io::Result<()> {
    match &tr[stmtid] {
        Stmt::Skip => writeln!(out, "{}skip()", "  ".repeat(index))?,
        Stmt::Block(t) => {
            for stmt_id in t.iter() {
                build_statements(out, tr, st, *stmt_id, index)?;
            }
        }
        Stmt::Assign(lhs, rhs) => writeln!(
            out,
            "{}{} := {};",
            "  ".repeat(index),
            st[lhs].full_name(st),
            serialize_expr(tr, st, &tr[rhs])
        )?,
        Stmt::Step => writeln!(out, "{}step();", "  ".repeat(index))?,
        Stmt::Fork => writeln!(out, "{}fork();", "  ".repeat(index))?,
        Stmt::While(cond, bodyid) => {
            writeln!(
                out,
                "{}while {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, &tr[cond])
            )?;
            build_statements(out, tr, st, *bodyid, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
        Stmt::IfElse(cond, ifbody, elsebody) => {
            writeln!(
                out,
                "{}if {} {{",
                "  ".repeat(index),
                serialize_expr(tr, st, &tr[cond])
            )?;
            build_statements(out, tr, st, *ifbody, index + 1)?;
            writeln!(out, "{}}} else {{", "  ".repeat(index))?;
            build_statements(out, tr, st, *elsebody, index + 1)?;
            writeln!(out, "{}}}", "  ".repeat(index))?;
        }
    }

    Ok(())
}

pub fn serialize(out: &mut impl Write, tr: &Transaction, st: &SymbolTable) -> std::io::Result<()> {
    write!(out, "fn {}(", tr.name)?;

    for (ii, arg) in tr.args.iter().enumerate() {
        let last_index = ii == tr.args.len() - 1;

        if last_index {
            write!(
                out,
                "{} {}: {}) {{\n",
                serialize_dir(arg),
                st[arg].name(),
                serialize_type(st[arg].tpe())
            )?;
        } else {
            write!(
                out,
                "{} {}: {}, ",
                serialize_dir(arg),
                st[arg].name(),
                serialize_type(st[arg].tpe())
            )?;
        }
    }

    build_statements(out, tr, st, tr.body, 1)?;

    writeln!(out, "}}")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use baa::BitVecValue;

    use super::*;
    use crate::ir::*;

    #[test]
    fn serialize_add_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let a = symbols.add("a".to_string(), Type::BitVec(32), None);
        let b: SymbolId = symbols.add("b".to_string(), Type::BitVec(32), None);
        let s = symbols.add("s".to_string(), Type::BitVec(32), None);
        assert_eq!(symbols["s"], symbols[s]);
        let dut = symbols.add("dut".to_string(), Type::Dut, None);
        let dut_a = symbols.add("a".to_string(), Type::Unknown, Some(dut));
        let dut_b = symbols.add("b".to_string(), Type::Unknown, Some(dut));
        let dut_s = symbols.add("s".to_string(), Type::Unknown, Some(dut));
        assert_eq!(symbols["dut.s"], symbols[dut_s]);
        assert_eq!(symbols["s"], symbols[s]);

        // 2) create transaction
        let mut add = Transaction::new("add".to_string());
        add.args = vec![
            Arg::new(a, Dir::In),
            Arg::new(b, Dir::In),
            Arg::new(s, Dir::Out),
        ];

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

        println!("{}", serialize_to_string(&add, &symbols).unwrap());
    }

    #[test]
    fn serialize_calyx_go_down_transaction() {
        // Manually create the expected result of parsing `calyx_go_down`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let ii = symbols.add("ii".to_string(), Type::BitVec(32), None);
        let oo = symbols.add("oo".to_string(), Type::BitVec(32), None);
        assert_eq!(symbols["oo"], symbols[oo]);
        let dut = symbols.add("dut".to_string(), Type::Dut, None);
        let dut_ii = symbols.add("ii".to_string(), Type::Unknown, Some(dut));
        let dut_go = symbols.add("go".to_string(), Type::Unknown, Some(dut));
        let dut_done = symbols.add("done".to_string(), Type::Unknown, Some(dut));
        let dut_oo = symbols.add("oo".to_string(), Type::Unknown, Some(dut));
        assert_eq!(symbols["dut.oo"], symbols[dut_oo]);
        assert_eq!(symbols["oo"], symbols[oo]);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        let cond_expr = calyx_go_done.e(Expr::Equal(dut_done_expr, one_expr));
        let not_expr = calyx_go_done.e(Expr::Not(cond_expr));

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let body = vec![
            calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr)),
            calyx_go_done.s(Stmt::Assign(dut_go, one_expr)),
            calyx_go_done.s(Stmt::While(not_expr, wbody)),
            calyx_go_done.s(Stmt::Assign(dut_done, one_expr)),
            calyx_go_done.s(Stmt::Assign(dut_go, zero_expr)),
            calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care())),
            calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr)),
        ];

        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));
        println!("{}", serialize_to_string(&calyx_go_done, &symbols).unwrap());
    }

    #[test]
    fn serialize_easycond_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let a = symbols.add("a".to_string(), Type::BitVec(32), None);
        let b: SymbolId = symbols.add("b".to_string(), Type::BitVec(32), None);
        assert_eq!(symbols["b"], symbols[b]);
        let dut = symbols.add("dut".to_string(), Type::Dut, None);
        let dut_a = symbols.add("a".to_string(), Type::Unknown, Some(dut));
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
        println!("{}", serialize_to_string(&easycond, &symbols).unwrap());
    }
}
