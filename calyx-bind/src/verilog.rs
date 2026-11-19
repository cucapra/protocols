// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::Context;
use protocols::backends::{Reg, VerilogGen, monitor_pin_dir};
use protocols::frontend::Module;
use protocols::frontend::ast::Clock;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::proto_graph::{Action, NodeId, ProtoGraph};

const DUT_PREFIX: &str = "dut_";

#[allow(clippy::too_many_arguments)]
pub fn to_verilog(
    ctx: &mut Context,
    name: &str,
    m: &Module,
    reset_actions: Vec<Action>,
    pg: &ProtoGraph,
    done_state: NodeId,
    st: &SymbolTable,
    node_labels: &[String],
    regs: Vec<Reg>,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let state_labels = vec![];

    let vgen = VerilogGen::new(st, m, pg.clone(), state_labels, regs, monitor_pin_dir);

    // module I/O
    writeln!(
        out,
        "// this file was generated from a protocol using calyx-bind"
    )?;
    vgen.module_header(name, out)?;

    // TODO: calyx control pins
    verilog_dut_instance(m, "  ", out)?;
    // dut_pin_binding(m, pg, vegn);
    writeln!(out)?;

    // TODO: special reset stuff

    // TODO: connect output pins

    // connect done pin
    writeln!(out, "  // done is true iff we are in the done state")?;
    writeln!(
        out,
        "  assign done = state == ???;",
        // state_labels[done_state.as_u32() as usize]
    )?;
    writeln!(out)?;

    vgen.registers(st, ctx, out)?;
    vgen.state_machine(st, ctx, out)?;
    writeln!(out, "endmodule")?;
    Ok(())
}

fn verilog_dut_instance(
    m: &Module,
    indent: &str,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    // declare I/O
    for pin in &m.pins {
        writeln!(
            out,
            "{indent}{} {DUT_PREFIX}{}; // {:?}",
            VerilogGen::logic(pin.bitwidth()),
            pin.name(),
            pin.dir()
        )?;
    }
    writeln!(out)?;

    // create module instance
    writeln!(out, "{indent}{} {}_inst (", m.name, m.name)?;
    match &m.clock {
        Clock::None => {}
        Clock::PosEdge(name) | Clock::NegEdge(name) => {
            writeln!(out, "{indent}  .{name} (clk),")?;
        }
    }
    let connects: Vec<_> = m
        .pins
        .iter()
        .map(|pin| format!("{indent}  .{} ({DUT_PREFIX}{})", pin.name(), pin.name()))
        .collect();
    writeln!(out, "{}", connects.join(",\n"))?;
    writeln!(out, "{indent});")?;

    Ok(())
}
