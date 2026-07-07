// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecOps, BitVecValue};
use rustc_hash::FxHashMap;

use crate::frontend::ast::*;
use crate::frontend::design::{Design, find_designs};
use crate::frontend::symbol::{Dir, SymbolId, SymbolTable};
use crate::scheduler::Invocation;

// todo: add `interface` and `module` to protocol language and remove pin argument
pub fn to_verilog(
    testbench_name: &str,
    ast: &Ast,
    pins: &[(String, PinAnnotation)],
    vcd_out: Option<&str>,
    invocs: &[Invocation],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let modules = find_designs(ast);
    let st = &ast.st;
    assert_eq!(
        modules.len(),
        1,
        "Currently we only handle a single modules."
    );
    let (_, module) = modules.into_iter().next().unwrap();

    // derive the instance name from the first protocol
    let first_proto_id = module.protocols[0].0;
    let instance_name_id = ast.protos[first_proto_id].type_param.unwrap();
    let instance_name = st[instance_name_id].name().to_string();

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
    for field in module.pins.iter() {
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
        .map(|f| f.name())
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
    for &(proto_id, _) in module.protocols.iter() {
        let proto = &ast.protos[proto_id];
        let sym_verilog = gen_sym_to_verilog_map(st, proto, &module, &instance_name);
        proto_to_verilog(st, proto, &sym_verilog, out)?;
    }

    // the test program
    writeln!(out, "  initial begin")?;
    if invocs.is_empty() {
        writeln!(out, "  // TODO: call transaction tasks from here")?;
    } else {
        for (ii, (name, args)) in invocs.iter().enumerate() {
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
                let arg: BitVecValue = arg.clone().try_into().unwrap();
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
    proto: &Protocol,
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
    proto: &Protocol,
    m: &Design,
    instance_name: &str,
) -> FxHashMap<SymbolId, String> {
    let mut out = FxHashMap::default();

    // transaction arguments are just flat identifiers with no prefixing
    for arg in proto.args.iter() {
        out.insert(arg.symbol(), st[arg.symbol()].name().to_string());
    }

    // dut ports get a prefix
    for (field_idx, field) in m.pins.iter().enumerate() {
        // symbols in each protocol all map to the same signal
        for (_, syms) in m.protocols.iter() {
            let sym = syms[field_idx];
            out.insert(sym, format!("{instance_name}_{}", field.name()));
        }
    }

    out
}

fn stmt_to_verilog(
    st: &SymbolTable,
    proto: &Protocol,
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
    proto: &Protocol,
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
    proto: &Protocol,
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
        Expr::Binary(BinOp::Add, a, b) => {
            write!(out, "(")?;
            expr_to_verilog(st, proto, sym_verilog, out, *a)?;
            write!(out, " + ")?;
            expr_to_verilog(st, proto, sym_verilog, out, *b)?;
            write!(out, ")")
        }
        Expr::Binary(BinOp::And, _, _) => {
            todo!("and")
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
        Expr::IsLastIteration => todo!("loops"),
        Expr::IterCount(_) => todo!("loops"),
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
        "Unknown symbol: {} ({s:?}).\nDid you mean: {:?}",
        st[s].full_name(st),
        sym_verilog
            .iter()
            .map(|(k, v)| format!(
                "{k:?} ({:?}.{}) -> {v}",
                st[k].scope_name(st),
                st[k].full_name(st)
            ))
            .collect::<Vec<_>>()
            .join(", ")
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
    use crate::frontend;
    use crate::frontend::diagnostic::DiagnosticHandler;

    fn backend(
        st: &SymbolTable,
        protos: &[Protocol],
        pins: &[(String, PinAnnotation)],
        invocs: &[Invocation],
    ) -> String {
        let mut out = vec![];
        to_verilog("tb", st, protos, pins, Some("dump.vcd"), invocs, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn alu_d1_to_verilog() {
        let (st, protos) = frontend(
            &["../tests/alus/alu_d1.prot"],
            &mut DiagnosticHandler::default(),
            false,
        )
        .unwrap();
        let tx = [
            (
                "add".into(),
                vec![
                    BitVecValue::from_i64(2, 32).into(),
                    BitVecValue::from_i64(5, 32).into(),
                    BitVecValue::from_i64(7, 32).into(),
                ],
            ),
            (
                "add".into(),
                vec![
                    BitVecValue::from_i64(34, 32).into(),
                    BitVecValue::from_i64(5, 32).into(),
                    BitVecValue::from_i64(39, 32).into(),
                ],
            ),
        ];
        let verilog = backend(
            &st,
            &protos,
            &[("clk".to_string(), PinAnnotation::Clock)],
            &tx,
        );
        println!("{verilog}");
        // note: this "test" just runs the Verilog backend, but it isn't really possible to
        //       assert meaningful properties about the output. That needs to be done by an
        //       end-to-end test.
    }
}
