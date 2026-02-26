// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::design::find_designs;
use crate::ir::*;
use crate::scheduler::TodoItem;
use baa::{BitVecOps, BitVecValue};

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
    if !pins.is_empty() {
        todo!("deal with extra pins");
    }

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
        writeln!(out, "")?;
    }

    // we always generate a clock even if it is not used
    writeln!(out, "  // clock with period = 2")?;
    writeln!(out, "  reg clk = 0;")?;
    writeln!(out, "  always #1 clk = ~clk;\n")?;
    writeln!(out, "")?;

    // variable used to control when the next protocol execution needs to be launched
    writeln!(
        out,
        "  // pulsing this wire will launch the next transaction"
    )?;
    writeln!(out, "  reg do_fork = 0;")?;
    writeln!(out, "")?;

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
    writeln!(out, "")?;

    // instance
    writeln!(out, "  // instance of the design under test")?;
    writeln!(out, "  {} {}(", module.name, instance_name)?;
    for (ii, (_, field)) in module.pins.iter().enumerate() {
        let is_first = ii == 0;
        if !is_first {
            writeln!(out, ",")?;
        }
        write!(
            out,
            "    .{}({}_{})",
            field.name(),
            instance_name,
            field.name()
        )?;
    }
    writeln!(out, "")?;
    writeln!(out, "  );")?;
    writeln!(out, "")?;

    // one task for each protocol
    for &proto_id in module.transaction_ids.iter() {
        let (proto, st) = &protos[proto_id];
        proto_to_verilog(st, proto, out)?;
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
                writeln!(out, "    wait(do_fork == 1);")?;
            }
            write!(out, "    {name}(")?;
            for (ii, arg) in args.iter().enumerate() {
                let is_first = ii == 0;
                if !is_first {
                    write!(out, ", ")?;
                }
                write!(out, "'h{}", arg.to_hex_str())?;
            }
            writeln!(out, ");")?;
        }
    }
    writeln!(out, "    #20;")?;
    writeln!(out, "    $finish();")?;
    writeln!(out, "  end")?;

    writeln!(out, "")?;

    writeln!(out, "endmodule // {testbench_name}")?;

    Ok(())
}

fn proto_to_verilog(
    st: &SymbolTable,
    proto: &Transaction,
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

    writeln!(out, "  endtask; // {}", proto.name)?;
    writeln!(out, "")?;
    Ok(())
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
    use crate::parser::Rule::assert_eq;
    use crate::parser::parse_file;
    use crate::typecheck::type_check;
    use clap::ColorChoice;

    fn frontend(filename: impl AsRef<std::path::Path>) -> Vec<(Transaction, SymbolTable)> {
        // Note: for the monitor, error message locations in `.prot` files are suppressed
        // in the `DiagnosticHandlers` for now
        let mut protocols_handler = DiagnosticHandler::new(ColorChoice::Auto, true, false, false);

        // Parse protocols file
        let transactions_symbol_tables: Vec<(Transaction, SymbolTable)> =
            parse_file(filename, &mut protocols_handler).unwrap();

        // Type-check the parsed transactions
        type_check(&transactions_symbol_tables, &mut protocols_handler).unwrap();

        transactions_symbol_tables
    }

    fn backend(
        protos: &[(Transaction, SymbolTable)],
        pins: &[(String, PinAnnotation)],
        transactions: &[TodoItem],
    ) -> String {
        let mut out = vec![];
        to_verilog("tb", protos, pins, Some("dump.vcd"), transactions, &mut out);
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn add_d1_to_verilog() {
        let protos = frontend("tests/adders/adder_d1/add_d1.prot");
        let tx = [(
            "add".into(),
            vec![
                BitVecValue::from_i64(2, 32),
                BitVecValue::from_i64(5, 32),
                BitVecValue::from_i64(7, 32),
            ],
        )];
        let verilog = backend(&protos, &[], &tx);
        println!("{verilog}");
        todo!("actually assert something!")
    }
}
