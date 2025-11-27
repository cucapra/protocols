// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use crate::{interpreter::ExprValue, ir::*};
use baa::{BitVecOps, BitVecValue};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::io::Write;

/// Serializes a `Vec` of `(Transaction, SymbolTable)` pairs to a `String`
pub fn serialize_to_string(trs: Vec<(Transaction, SymbolTable)>) -> std::io::Result<String> {
    let mut out = Vec::new();
    serialize(&mut out, trs)?;
    let out = String::from_utf8(out).unwrap();
    Ok(out)
}

/// Pretty prints a `type` with respect to the current `SymbolTable`
pub fn serialize_type(st: &SymbolTable, tpe: Type) -> String {
    match tpe {
        Type::BitVec(t) => format!("u{}", t),
        Type::Struct(structid) => st[structid].name().to_owned(),
        Type::Unknown => "unknown".to_string(),
    }
}

/// Pretty-prints a `Field` with respect to the current `SymbolTable`
pub fn serialize_field(st: &SymbolTable, field: &Field) -> String {
    format!(
        "{} {}: {}",
        field.dir(),
        field.name(),
        serialize_type(st, field.tpe())
    )
}

/// Pretty prints a `Direction`
impl std::fmt::Display for Dir {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Dir::In => write!(f, "in"),
            Dir::Out => write!(f, "out"),
        }
    }
}

/// Pretty-printer for `BinaryOp`s
impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Equal => write!(f, "=="),
            BinOp::Concat => write!(f, "+"),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),
        }
    }
}

/// Pretty-printer for `ExprValue`s
impl std::fmt::Display for ExprValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprValue::Concrete(bit_vec_value) => write!(f, "{:?}", bit_vec_value),
            ExprValue::DontCare => write!(f, "DontCare"),
        }
    }
}

/// Pretty-printer for `UnaryOp`s
impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "!")
    }
}

/// Serializes a bit-vector value. If `display_hex = true`,
/// the bit-vector is printed in hexadecimal, otherwise it is displayed
/// in decimal.
pub fn serialize_bitvec(bv: &BitVecValue, display_hex: bool) -> String {
    if display_hex {
        format!("0x{}", bv.to_hex_str())
    } else {
        bv.to_dec_str()
    }
}

/// Pretty-prints the arguments map, where `SymbolId`s are rendered using
/// the corresponding string variable name according to the `SymbolTable`.
/// When printing, we sort the keys by lexicographic order of variable names
/// (to ensure a canonical serialization format).
/// The `display_hex` argument indicates whether to display integer literals
/// using hexadeimcal (if `false`, we default to using decimal).
pub fn serialize_args_mapping(
    args_mapping: &FxHashMap<SymbolId, BitVecValue>,
    symbol_table: &SymbolTable,
    display_hex: bool,
) -> String {
    args_mapping
        .iter()
        .sorted_by_key(|(symbol_id, _)| symbol_table[*symbol_id].name())
        .map(|(symbol_id, value)| {
            format!(
                "({}) {}: {}",
                symbol_id,
                symbol_table[*symbol_id].name(),
                serialize_bitvec(value, display_hex)
            )
        })
        .collect::<Vec<String>>()
        .join("\n")
}

/// Pretty-prints an `Expression` (identified by its `ExprId`) using the current
/// `Transaction` and `SymbolTable`
pub fn serialize_expr(tr: &Transaction, st: &SymbolTable, expr_id: &ExprId) -> String {
    match &tr[expr_id] {
        Expr::Const(val) => val.to_u64().unwrap().to_string(),
        Expr::Sym(symid) => st[symid].full_name(st),
        Expr::DontCare => "X".to_string(),
        Expr::Unary(unary_op, expr_id) => {
            let e = serialize_expr(tr, st, expr_id);
            format!("{}({})", unary_op, e)
        }
        Expr::Binary(op, lhs, rhs) => {
            let e1 = serialize_expr(tr, st, lhs);
            let e2 = serialize_expr(tr, st, rhs);
            format!("{e1} {op} {e2}")
        }
        Expr::Slice(expr, idx1, idx2) => {
            let e = serialize_expr(tr, st, expr);
            let i = idx1.to_string();
            if *idx2 == *idx1 {
                format!("{}[{}]", e, i)
            } else {
                let j = idx2.to_string();
                format!("{}[{}:{}]", e, i, j)
            }
        }
    }
}

/// Pretty-prints a `Statement` (identified by its `StmtId`) using the current
/// `Transaction` and `SymbolTable`
pub fn serialize_stmt(tr: &Transaction, st: &SymbolTable, stmt_id: &StmtId) -> String {
    match &tr[stmt_id] {
        Stmt::Block(stmt_ids) => {
            // Only print the at most 2 statements in a block for brevity
            let num_stmts = std::cmp::min(2, stmt_ids.len());
            let formatted_stmts = stmt_ids[..num_stmts]
                .iter()
                .map(|stmt_id| serialize_stmt(tr, st, stmt_id))
                .collect::<Vec<_>>()
                .join("; ");
            if num_stmts < 2 {
                format!("{};", formatted_stmts)
            } else {
                format!("{{ {}; ... }}", formatted_stmts)
            }
        }
        Stmt::Assign(symbol_id, expr_id) => {
            format!(
                "{} := {}",
                st.full_name_from_symbol_id(symbol_id),
                serialize_expr(tr, st, expr_id)
            )
        }
        Stmt::Step => "step()".to_string(),
        Stmt::Fork => "fork()".to_string(),
        Stmt::While(expr_id, stmt_id) => {
            format!(
                "while {} {{ {} }}",
                serialize_expr(tr, st, expr_id),
                serialize_stmt(tr, st, stmt_id)
            )
        }
        Stmt::IfElse(expr_id, stmt_id1, stmt_id2) => {
            format!(
                "if {} {{ {} }} {{ {} }}",
                serialize_expr(tr, st, expr_id),
                serialize_stmt(tr, st, stmt_id1),
                serialize_stmt(tr, st, stmt_id2)
            )
        }
        Stmt::AssertEq(expr_id1, expr_id2) => {
            format!(
                "assert_eq({}, {})",
                serialize_expr(tr, st, expr_id1),
                serialize_expr(tr, st, expr_id2)
            )
        }
    }
}

/// Pretty-prints a `Statement` (identified by its `StmtId`) using the
/// provided `Transaction` and `SymbolTable` using the provided output buffer `out`,
/// with the amount of indentation specified by `index`
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
        Stmt::Step => writeln!(out, "{}step();", "  ".repeat(index),)?,
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

/// Pretty prints the definition of a struct type definition
/// to the output buffer `out`
pub fn serialize_structs(
    out: &mut impl Write,
    st: &SymbolTable,
    struct_ids: Vec<StructId>,
) -> std::io::Result<()> {
    for struct_id in struct_ids {
        writeln!(out, "struct {} {{", st[struct_id].name())?;

        for field in st[struct_id].pins() {
            writeln!(
                out,
                "  {} {}: {},",
                field.dir(),
                field.name(),
                serialize_type(st, field.tpe())
            )?;
        }
        writeln!(out, "}}\n")?;
    }

    Ok(())
}

/// Serializes a `Vec` of `(SymbolTable, Transaction)` pairs to the provided
/// output buffer `out`
pub fn serialize(
    out: &mut impl Write,
    trs: Vec<(Transaction, SymbolTable)>,
) -> std::io::Result<()> {
    let (_, st) = &trs[0];

    if !st.struct_ids().is_empty() {
        serialize_structs(out, st, st.struct_ids())?;
    }

    for (tr, st) in trs {
        write!(out, "fn {}", tr.name)?;

        if let Some(type_param) = tr.type_param {
            write!(
                out,
                "<{}: {}>",
                st[type_param].name(),
                serialize_type(&st, st[type_param].tpe())
            )?;
        }

        write!(out, "(")?;

        if tr.args.is_empty() {
            writeln!(out, ") {{")?;
        } else {
            for (ii, arg) in tr.args.iter().enumerate() {
                let last_index = ii == tr.args.len() - 1;

                if last_index {
                    writeln!(
                        out,
                        "{} {}: {}) {{",
                        arg.dir(),
                        st[arg].name(),
                        serialize_type(&st, st[arg].tpe())
                    )?;
                } else {
                    write!(
                        out,
                        "{} {}: {}, ",
                        arg.dir(),
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
    use baa::BitVecValue;
    use insta::Settings;
    use std::path::Path;
    use strip_ansi_escapes::strip_str;

    use super::*;
    use crate::diagnostic::DiagnosticHandler;
    use crate::parser::parse_file;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    fn test_helper(filename: &str, snap_name: &str) {
        let mut handler = DiagnosticHandler::default();
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
        test_helper("tests/adders/adder_d1/add_d1.prot", "add_d1");
    }

    #[test]
    fn test_calyx_go_done_transaction() {
        test_helper(
            "tests/calyx_go_done/calyx_go_done_struct.prot",
            "calyx_go_done_struct",
        );
    }

    #[test]
    fn test_invalid_lex_prot() {
        test_helper("tests/misc/invalid_lex.prot", "invalid_lex");
    }

    #[test]
    fn test_aes128_prot() {
        test_helper("examples/tinyaes128/aes128.prot", "aes128");
    }

    #[test]
    fn test_aes128_round_prot() {
        test_helper("examples/tinyaes128/aes128_round.prot", "aes128_round");
    }

    #[test]
    fn test_aes128_expand_key_prot() {
        test_helper(
            "examples/tinyaes128/aes128_expand_key.prot",
            "aes128_expand_key",
        );
    }

    #[test]
    fn test_mul_invalid_prot() {
        test_helper("tests/multipliers/mul_invalid.prot", "mul_invalid");
    }

    #[test]
    fn test_mul_prot() {
        test_helper("tests/multipliers/mul.prot", "mul");
    }

    #[test]
    fn test_mul_ignore_prot() {
        test_helper("tests/multipliers/mul_ignore.prot", "mul_ignore");
    }

    #[test]
    fn test_cond_prot() {
        test_helper("tests/multipliers/mult_cond.prot", "cond");
    }

    #[test]
    fn test_parse_serv_register_file_prot() {
        test_helper(
            "examples/serv/serv_regfile.prot",
            "parse_serv_register_file",
        );
    }

    #[test]
    fn test_illegal_fork_prot() {
        test_helper("tests/adders/illegal_fork.prot", "illegal_fork_prot");
    }

    #[test]
    fn test_invalid_step_arg() {
        test_helper("tests/misc/invalid_step_arg.prot", "invalid_step_arg");
    }

    #[test]
    fn test_func_arg_invalid_prot() {
        test_helper("tests/misc/func_arg_invalid.prot", "func_arg_invalid_prot");
    }

    #[test]
    fn test_simple_if_transaction() {
        test_helper("tests/counters/simple_if.prot", "simple_if");
    }

    #[test]
    fn test_simple_while_transaction() {
        test_helper("tests/counters/simple_while.prot", "simple_while");
    }

    #[test]
    fn test_simple_if_without_else_transaction() {
        test_helper(
            "tests/identities/dual_identity_d1/if_without_else.prot",
            "if_without_else",
        );
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
            "Dummy".to_string(),
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
        easycond.type_param = Some(dut);

        // 3) create expressions
        let a_expr = easycond.e(Expr::Sym(a));
        let dut_a_expr = easycond.e(Expr::Sym(dut_a));

        let one_expr = easycond.e(Expr::Const(BitVecValue::from_i64(1, 2)));
        let cond_expr = easycond.e(Expr::Binary(BinOp::Equal, dut_a_expr, one_expr));

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
            serialize_to_string(vec![(easycond, symbols)]).unwrap()
        );
    }
}
