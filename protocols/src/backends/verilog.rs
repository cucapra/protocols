// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::design::{Design, find_designs};
use crate::ir::*;
use crate::scheduler::TodoItem;
use baa::{BitVecOps, BitVecValue};
use rustc_hash::FxHashMap;

// todo: add `interface` and `module` to protocol language and remove pin argument
pub fn to_verilog(
    testbench_name: &str,
    protos: &[(Transaction, SymbolTable)],
    pins: &[(String, PinAnnotation)],
    vcd_out: Option<&str>,
    transactions: &[TodoItem],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let modules = find_designs(protos.iter());
    assert_eq!(
        modules.len(),
        1,
        "Currently we only handle a single modules."
    );
    let (_, module) = modules.into_iter().next().unwrap();

    // derive the instance name from the first protocol
    let first_proto_id = *module.transaction_ids.first().unwrap();
    // for the design we can use any symbol table
    let instance_name_id = protos[first_proto_id].0.type_param.unwrap();
    let design_sym_tb = protos[first_proto_id].1.clone();
    let instance_name = design_sym_tb[instance_name_id].name().to_string();

    // header
    writeln!(out, "// Testbench generated with protocols")?;
    writeln!(out, "module {testbench_name};")?;

    // VCD output
    if let Some(filename) = vcd_out {
        writeln!(out, "  // VCD output")?;
        writeln!(
            out,
            "  initial begin $dumpfile(\"{filename}\"); $dumpvars(0, {testbench_name}); end "
        )?;
        writeln!(out)?;
    }

    // we always generate a clock even if it is not used
    writeln!(out, "  // clock with period = 2")?;
    writeln!(out, "  reg clk = 0;")?;
    writeln!(out, "  always #1 clk = ~clk;\n")?;
    writeln!(out)?;

    // variable used to control when the next protocol execution needs to be launched
    writeln!(
        out,
        "  // pulsing this wire will launch the next transaction"
    )?;
    writeln!(out, "  reg [31:0] do_fork_count = 0;")?;
    writeln!(out, "  reg [31:0] started_count = 0;")?;
    writeln!(out, "  reg [31:0] finished_count = 0;")?;
    writeln!(out)?;

    // pins
    writeln!(
        out,
        "  // variables for the pins of {} : {}",
        instance_name, module.name
    )?;
    for (_, field) in module.pins.iter() {
        match field.dir() {
            Dir::In => writeln!(
                out,
                "  reg [{}:0] {}_{};",
                field.bitwidth() - 1,
                instance_name,
                field.name()
            )?,
            Dir::Out => writeln!(
                out,
                "  wire [{}:0] {}_{};",
                field.bitwidth() - 1,
                instance_name,
                field.name()
            )?,
        }
    }
    // extra pins
    for (name, anno) in pins {
        match anno {
            PinAnnotation::Clock => {
                writeln!(out, "  wire {}_{}; // Clock input", instance_name, name)?;
                writeln!(out, "  assign {}_{} = clk;", instance_name, name)?;
            }
            PinAnnotation::Const(value) => {
                writeln!(
                    out,
                    "  wire [{}:0] {}_{}; // Constant input",
                    value.width() - 1,
                    instance_name,
                    name
                )?;
                writeln!(
                    out,
                    "  assign {}_{} = 'h{};",
                    instance_name,
                    name,
                    value.to_hex_str()
                )?;
            }
        }
    }
    writeln!(out)?;

    // instance
    writeln!(out, "  // instance of the design under test")?;
    writeln!(out, "  {} {}(", module.name, instance_name)?;
    let pin_names = module
        .pins
        .iter()
        .map(|(_, f)| f.name())
        .chain(pins.iter().map(|(n, _)| n.as_str()));
    for (ii, name) in pin_names.enumerate() {
        let is_first = ii == 0;
        if !is_first {
            writeln!(out, ",")?;
        }
        write!(out, "    .{}({}_{})", name, instance_name, name)?;
    }
    writeln!(out)?;
    writeln!(out, "  );")?;
    writeln!(out)?;

    // one task for each protocol
    for &proto_id in module.transaction_ids.iter() {
        let (proto, st) = &protos[proto_id];
        let sym_verilog = gen_sym_to_verilog_map(st, proto, &module, &instance_name);
        proto_to_verilog(st, proto, &sym_verilog, out)?;
    }

    // the test program
    writeln!(out, "  initial begin")?;
    if transactions.is_empty() {
        writeln!(out, "  // TODO: call transaction tasks from here")?;
    } else {
        for (ii, (name, args)) in transactions.iter().enumerate() {
            let has_prev = ii > 0;
            if has_prev {
                writeln!(
                    out,
                    "    #2; // we need to wait at least one clock cycle before the next transaction can be started"
                )?;
                writeln!(out, "    wait(do_fork_count >= started_count);")?;
            }
            writeln!(out, "    started_count += 'd1;")?;
            write!(out, "    fork {name}(")?;
            for (ii, arg) in args.iter().enumerate() {
                let is_first = ii == 0;
                if !is_first {
                    write!(out, ", ")?;
                }
                write!(out, "'h{}", arg.to_hex_str())?;
            }
            writeln!(out, "); join_none")?;
        }
    }
    writeln!(out, "    wait(started_count == finished_count);")?;
    writeln!(out, "    #2;")?;
    writeln!(out, "    $finish();")?;
    writeln!(out, "  end")?;

    writeln!(out)?;

    writeln!(out, "endmodule // {testbench_name}")?;

    Ok(())
}

fn proto_to_verilog(
    st: &SymbolTable,
    proto: &Transaction,
    sym_verilog: &FxHashMap<SymbolId, String>,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    writeln!(out, "  // protocol: {}", proto.name)?;
    write!(out, "  task automatic {}(", proto.name)?;
    for (ii, arg) in proto.args.iter().enumerate() {
        let is_first = ii == 0;
        if !is_first {
            write!(out, ", ")?;
        }
        let arg_tpe = st[arg.symbol()].tpe();
        let arg_name = st[arg.symbol()].name();
        write!(out, "input [{}:0] {}", arg_tpe.bitwidth() - 1, arg_name)?;
    }
    writeln!(out, ");")?;

    stmt_to_verilog(st, proto, "    ", sym_verilog, out, proto.body)?;

    writeln!(out, "    finished_count += 1;")?;
    writeln!(out, "  endtask; // {}", proto.name)?;
    writeln!(out)?;
    Ok(())
}

fn gen_sym_to_verilog_map(
    st: &SymbolTable,
    proto: &Transaction,
    m: &Design,
    instance_name: &str,
) -> FxHashMap<SymbolId, String> {
    let mut out = FxHashMap::default();

    // transaction arguments are just flat identifiers with no prefixing
    for arg in proto.args.iter() {
        out.insert(arg.symbol(), st[arg.symbol()].name().to_string());
    }

    // dut ports get a prefix
    for (sym, field) in m.pins.iter() {
        out.insert(*sym, format!("{instance_name}_{}", field.name()));
    }

    out
}

fn stmt_to_verilog(
    st: &SymbolTable,
    proto: &Transaction,
    indent: &str,
    sym_verilog: &FxHashMap<SymbolId, String>,
    out: &mut impl std::io::Write,
    stmt: StmtId,
) -> std::io::Result<()> {
    match &proto[stmt] {
        Stmt::Block(stmts) => {
            for s in stmts {
                stmt_to_verilog(st, proto, indent, sym_verilog, out, *s)?;
            }
        }
        Stmt::Assign(lhs, rhs) => {
            write!(out, "{indent}")?;
            sym_to_verilog(st, sym_verilog, out, lhs)?;
            write!(out, " = ")?;
            expr_to_verilog(st, proto, sym_verilog, out, *rhs)?;
            writeln!(out, ";")?;
        }
        Stmt::Step => {
            writeln!(out, "{indent}#2; // step()")?;
        }
        Stmt::Fork => {
            writeln!(out, "{indent}do_fork_count += 1; // fork()")?;
        }
        Stmt::While(_, _) => {
            todo!("while loop")
        }
        Stmt::RepeatLoop(_, _) => {
            todo!("repeat loop")
        }
        Stmt::ForInLoop(_, _, _) => {
            todo!("for-in loop")
        }
        Stmt::IfElse(_, _, _) => {
            todo!("if/else")
        }
        Stmt::AssertEq(a, b) => {
            assert_eq_to_verilog(st, proto, indent, sym_verilog, out, *a, *b)?;
        }
    }
    Ok(())
}

fn assert_eq_to_verilog(
    st: &SymbolTable,
    proto: &Transaction,
    indent: &str,
    sym_verilog: &FxHashMap<SymbolId, String>,
    out: &mut impl std::io::Write,
    a: ExprId,
    b: ExprId,
) -> std::io::Result<()> {
    // print out error
    write!(out, "{indent}if (")?;
    expr_to_verilog(st, proto, sym_verilog, out, a)?;
    write!(out, " != ")?;
    expr_to_verilog(st, proto, sym_verilog, out, b)?;
    writeln!(out, ")")?;
    write!(out, "{indent}  $display (\"[%0t] {}(", proto.name)?;
    for ii in 0..proto.args.len() {
        let is_first = ii == 0;
        if !is_first {
            write!(out, ", 0x%0h")?;
        } else {
            write!(out, "0x%0h")?;
        }
    }
    write!(out, "): ")?;
    expr_to_verilog(st, proto, sym_verilog, out, a)?;
    write!(out, "=0x%0h ")?;
    expr_to_verilog(st, proto, sym_verilog, out, b)?;
    write!(out, "=0x%0h\", $time, ")?;
    for arg in proto.args.iter() {
        let arg_name = st[arg.symbol()].name();
        write!(out, "{arg_name}, ")?;
    }
    expr_to_verilog(st, proto, sym_verilog, out, a)?;
    write!(out, ", ")?;
    expr_to_verilog(st, proto, sym_verilog, out, b)?;
    writeln!(out, ");")?;

    // actual assert
    write!(out, "{indent}assert(")?;
    expr_to_verilog(st, proto, sym_verilog, out, a)?;
    write!(out, " == ")?;
    expr_to_verilog(st, proto, sym_verilog, out, b)?;
    writeln!(out, ");")?;

    Ok(())
}

fn expr_to_verilog(
    st: &SymbolTable,
    proto: &Transaction,
    sym_verilog: &FxHashMap<SymbolId, String>,
    out: &mut impl std::io::Write,
    e: ExprId,
) -> std::io::Result<()> {
    match &proto[e] {
        Expr::Const(value) => write!(out, "'h{}", value.to_hex_str()),
        Expr::Sym(s) => sym_to_verilog(st, sym_verilog, out, s),
        Expr::DontCare => write!(out, "$random"),
        Expr::Binary(BinOp::Equal, a, b) => {
            write!(out, "(")?;
            expr_to_verilog(st, proto, sym_verilog, out, *a)?;
            write!(out, " == ")?;
            expr_to_verilog(st, proto, sym_verilog, out, *b)?;
            write!(out, ")")
        }
        Expr::Binary(BinOp::Concat, a, b) => {
            write!(out, "{{")?;
            expr_to_verilog(st, proto, sym_verilog, out, *a)?;
            write!(out, ", ")?;
            expr_to_verilog(st, proto, sym_verilog, out, *b)?;
            write!(out, "}}")
        }
        Expr::Unary(UnaryOp::Not, e) => {
            write!(out, "~")?;
            expr_to_verilog(st, proto, sym_verilog, out, *e)
        }
        Expr::Slice(e, msb, lsb) => {
            write!(out, "(")?;
            expr_to_verilog(st, proto, sym_verilog, out, *e)?;
            if msb == lsb {
                write!(out, ")[{msb}]")
            } else {
                write!(out, ")[{msb}:{lsb}]")
            }
        }
    }
}

fn sym_to_verilog(
    st: &SymbolTable,
    sym_verilog: &FxHashMap<SymbolId, String>,
    out: &mut impl std::io::Write,
    s: &SymbolId,
) -> std::io::Result<()> {
    debug_assert!(
        sym_verilog.contains_key(s),
        "Unknown symbol: {} ({s:?})",
        st[s].full_name(st)
    );
    write!(out, "{}", sym_verilog[s])
}

#[derive(Debug, Clone, PartialOrd, PartialEq)]
pub enum PinAnnotation {
    Clock,
    Const(BitVecValue),
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::diagnostic::DiagnosticHandler;
    use crate::frontend;

    fn backend(
        protos: &[(Transaction, SymbolTable)],
        pins: &[(String, PinAnnotation)],
        transactions: &[TodoItem],
    ) -> String {
        let mut out = vec![];
        to_verilog("tb", protos, pins, Some("dump.vcd"), transactions, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn alu_d1_to_verilog() {
        let protos = frontend(
            "tests/alus/alu_d1.prot",
            &mut DiagnosticHandler::default(),
            false,
        )
        .unwrap();
        let tx = [
            (
                "add".into(),
                vec![
                    BitVecValue::from_i64(2, 32),
                    BitVecValue::from_i64(5, 32),
                    BitVecValue::from_i64(7, 32),
                ],
            ),
            (
                "add".into(),
                vec![
                    BitVecValue::from_i64(34, 32),
                    BitVecValue::from_i64(5, 32),
                    BitVecValue::from_i64(39, 32),
                ],
            ),
        ];
        let verilog = backend(&protos, &[("clk".to_string(), PinAnnotation::Clock)], &tx);
        println!("{verilog}");
        // note: this "test" just runs the Verilog backend, but it isn't really possible to
        //       assert meaningful properties about the output. That needs to be done by an
        //       end-to-end test.
    }
}
