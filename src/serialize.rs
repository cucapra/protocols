use std::{any::Any, io::Write};

use crate::ir::{
    Arg,
    Dir::*,
    Expr,
    Expr::*,
    Stmt::*,
    StmtId, SymbolTable, Transaction,
    Type::{self, *},
};

pub fn serialize_to_string(tr: &Transaction, st: &SymbolTable) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, tr, st)?;
    let out = String::from_utf8(out).unwrap();
    Ok(out)
}

// TODO need to fix for other types
pub fn find_type(tpe: Type) -> String {
    match tpe {
        BitVec(t) => "u".to_owned() + &t.to_string(),
        Dut => "dut".to_string(),
        Unknown => "unknown".to_string(),
    }
}

pub fn find_dir(el: &Arg) -> String {
    match el.dir() {
        In => "in".to_string(),
        Out => "out".to_string(),
    }
}

pub fn find_expr(tr: &Transaction, st: &SymbolTable, expr: &Expr) -> String {
    match expr {
        Sym(symid) => st[symid].full_name(st),
        DontCare => "X".to_owned(),
        Not(expid) => "!".to_owned() + &find_expr(tr, st, &tr[expid]),
        And(expid1, expid2) => find_expr(tr, st, &tr[expid1]) + " && " + &find_expr(tr, st, &tr[expid2]),
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
        Skip => writeln!(out, "{}skip()", "  ".repeat(index))?,
        Block(t) => {
            for stmt_id in t.iter() {
                build_statements(out, tr, st, *stmt_id, index+1)?;
            }
        }
        Assign(a, b) => writeln!(out, "{}{} := {};", "  ".repeat(index), st[a].full_name(st), find_expr(tr, st, &tr[b]))?,
        Step => writeln!(out, "{}step();", "  ".repeat(index))?,
        Fork => writeln!(out, "{}fork();", "  ".repeat(index))?,
        While(a, b) => writeln!(out, "while")?,
        IfElse(a, b, c) => writeln!(out, "ifelse")?,
    }

    Ok(())
}

pub fn serialize(out: &mut impl Write, tr: &Transaction, st: &SymbolTable) -> std::io::Result<()> {
    write!(out, "fn {}(", tr.name)?;

    let mut arguments = tr.args.iter().peekable();

    while let Some(arg) = arguments.next() {
        if arguments.peek().is_none() {
            write!(
                out,
                "{} {}: {}) {{\n",
                find_dir(arg),
                st[arg].name(),
                find_type(st[arg].tpe())
            )?;
        } else {
            write!(
                out,
                "{} {}: {}, ",
                find_dir(arg),
                st[arg].name(),
                find_type(st[arg].tpe())
            )?;
        }
    }

    build_statements(out, tr, st, tr.body, 1)?;

    writeln!(out, "}}")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::*;

    #[test]
    fn serialize_add_transaction() {
        // Manually create the expected result of parsing `add.prot`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let a = symbols.add("a".to_string(), Type::BitVec(32), None);
        let b = symbols.add("b".to_string(), Type::BitVec(32), None);
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
}
