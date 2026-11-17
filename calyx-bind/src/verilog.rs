// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{SmallVecExprRef, op_port_width, proto_methods};
use patronus::expr::{Context, Expr, ExprRef};
use protocols::backends::VerilogGen;
use protocols::frontend::Module;
use protocols::frontend::ast::Clock;
use protocols::frontend::symbol::{Dir, SymbolId, SymbolKind, SymbolTable, Type};
use protocols::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::smallvec;

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
    auto_regs: &[(SymbolId, ExprRef, SymbolId)],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let vgen = VerilogGen::new(st, m, monitor, monitor_pin_dir);

    let keywords = FxHashSet::from_iter(VERILOG_KEYWORDS.iter().cloned());
    let mut symbol_names = FxHashMap::default();
    let mut expr_names = FxHashMap::default();

    // compute Verilog compatible names for all automaton registers
    for &(reg, ..) in auto_regs {
        let reg_name = st[reg].name().to_string();
        if let Some(name) = reg_name.strip_prefix("$monitor_") {
            let new_name = format!("_{name}");
            insert_symbol_name(reg, new_name, pg, &mut symbol_names, &mut expr_names);
        }
    }

    // module I/O
    writeln!(
        out,
        "// this file was generated from a protocol using calyx-bind"
    )?;
    writeln!(out, "module {name}(")?;
    writeln!(out, "  input  {} clk,   // global clock", logic(1))?;
    writeln!(
        out,
        "  input  {} reset, // 1-cycle active-high reset",
        logic(1)
    )?;
    writeln!(
        out,
        "  input  {} go,    // calyx standard control",
        logic(1)
    )?;
    let ops: Vec<_> = proto_methods(m)
        .enumerate()
        .map(|(i, p)| format!("{i}={}", p.name))
        .collect();
    writeln!(
        out,
        "  input  {} op,    // {}",
        logic(op_port_width(m)),
        ops.join(", ")
    )?;
    let arg_pin_info = arg_pins(st, m, auto_regs, &keywords, out)?;
    for pin in &arg_pin_info {
        for &ArgId {
            method_idx,
            arg_idx,
        } in &pin.ids
        {
            let arg_sym = proto_methods(m).nth(method_idx).unwrap().args[arg_idx].symbol();
            insert_symbol_name(
                arg_sym,
                pin.name.clone(),
                pg,
                &mut symbol_names,
                &mut expr_names,
            );
        }
    }
    writeln!(
        out,
        "  output {} done   // calyx standard control",
        logic(1)
    )?;
    writeln!(out, ");\n")?;

    verilog_dut_instance(m, "  ", out)?;
    dut_pin_binding(m, pg, &mut symbol_names, &mut expr_names);
    writeln!(out)?;

    let num_states = pg.nodes().count();
    assert_eq!(num_states, node_labels.len());
    let state_labels: Vec<_> = node_labels
        .iter()
        .map(|l| format!("ST_{}", l.to_uppercase()))
        .collect();
    let state_width = usize::BITS - num_states.leading_zeros();

    writeln!(out, "  typedef enum logic [{}:0] {{", state_width - 1)?;
    let entries: Vec<_> = state_labels
        .iter()
        .enumerate()
        .map(|(idx, lbl)| format!("    {lbl}  = {state_width}'d{idx}"))
        .collect();
    writeln!(out, "{}", entries.join(",\n"))?;
    writeln!(out, "  }} state_t;\n")?;
    writeln!(out, "  state_t state, next_state;")?;
    for (reg, ..) in auto_regs {
        let name = &symbol_names[reg];
        writeln!(
            out,
            "  {} {}, next_{};",
            logic(st[reg].tpe().bitwidth()),
            name,
            name,
        )?;
    }
    writeln!(out)?;
    // registers
    writeln!(out, "  always_ff @(posedge clk) begin")?;
    writeln!(out, "    if (reset) begin",)?;
    writeln!(
        out,
        "      state <= {};",
        state_labels[pg.entry.as_u32() as usize]
    )?;
    for (reg, value, _) in auto_regs {
        writeln!(
            out,
            "      {} <= {};",
            symbol_names[reg],
            expr_to_verilog(ctx, *value, &expr_names)
        )?;
    }
    writeln!(out, "    end else begin",)?;
    writeln!(out, "      state <= next_state;",)?;
    for (reg, _, _) in auto_regs {
        let name = &symbol_names[reg];
        writeln!(out, "      {name} <= next_{name};",)?;
    }
    writeln!(out, "    end",)?;
    writeln!(out, "  end\n",)?;

    // connect output pins
    writeln!(
        out,
        "  // connect output arguments to registers that capture them"
    )?;
    for pin in &arg_pin_info {
        if let Some(reg) = pin.output_reg {
            writeln!(out, "  assign {} = {};", pin.name, symbol_names[&reg])?;
        }
    }
    writeln!(out)?;

    // connect done pin
    writeln!(out, "  // done is true iff we are in the done state")?;
    writeln!(
        out,
        "  assign done = state == {};",
        state_labels[done_state.as_u32() as usize]
    )?;
    writeln!(out)?;

    // combinational
    writeln!(out, "  always_comb begin")?;
    writeln!(out, "    // register default to their previous values")?;
    writeln!(out, "    next_state = state;")?;
    for (reg, _, _) in auto_regs {
        let name = &symbol_names[reg];
        writeln!(out, "    next_{name} = {name};",)?;
    }
    writeln!(out)?;
    writeln!(out, "    // default values for dut inputs")?;
    let _assignments = assignment_expressions_by_target(pg);
    for pin in &m.pins {
        if pin.dir() == Dir::In {
            // TODO: we need to know all the symbols that this pin maps to
            writeln!(
                out,
                "    // TODO: find all the assignments to this particular pin for a better default assignment!"
            )?;
            writeln!(
                out,
                "    {DUT_PREFIX}{} = {}'d0;",
                pin.name(),
                pin.bitwidth()
            )?;
        }
    }
    writeln!(out)?;

    // reset
    writeln!(out, "    if (reset) begin")?;
    for act in &reset_actions {
        action_to_verilog(ctx, pg, st, act, "      ", &expr_names, &symbol_names, out)?;
    }
    writeln!(out, "    end else begin")?;
    // states
    writeln!(out, "      unique case (state)")?;
    for (idx, lbl) in state_labels.iter().enumerate() {
        writeln!(out, "      {lbl}: begin")?;
        let node_id = NodeId::from_u32(idx as u32);
        for act in &pg[node_id].actions {
            action_to_verilog(
                ctx,
                pg,
                st,
                act,
                "        ",
                &expr_names,
                &symbol_names,
                out,
            )?;
        }
        for tran in &pg[node_id].transitions {
            if tran.guard == ctx.get_false() || tran.target == node_id {
                continue;
            }

            if tran.guard != ctx.get_true() {
                writeln!(
                    out,
                    "        if ({})",
                    expr_to_verilog(ctx, tran.guard, &expr_names)
                )?;
                write!(out, "  ")?;
            }

            writeln!(
                out,
                "        next_state = {};",
                state_labels[tran.target.as_u32() as usize]
            )?;
        }
        writeln!(out, "      end")?;
    }
    writeln!(out, "      endcase")?;

    writeln!(out, "    end")?;

    writeln!(out, "  end")?;
    writeln!(out, "endmodule")?;

    Ok(())
}

fn assignment_expressions_by_target(pg: &ProtoGraph) -> FxHashMap<SymbolId, SmallVecExprRef> {
    let mut out = FxHashMap::default();
    for act in pg.nodes().flat_map(|(_, node)| node.actions.iter()) {
        if let Op::Assign(sym, assign) = &pg[act.op] {
            let vec = out.entry(*sym).or_insert_with(|| smallvec![]);
            for (_, expr) in &assign.concretes {
                vec.push(*expr);
            }
        }
    }
    out
}

#[derive(Debug)]
struct ArgPin {
    #[allow(dead_code)]
    ids: Vec<ArgId>,
    name: String,
    output_reg: Option<SymbolId>,
}

#[derive(Debug)]
struct ArgId {
    #[allow(dead_code)]
    method_idx: usize,
    #[allow(dead_code)]
    arg_idx: usize,
}

fn arg_pins(
    st: &SymbolTable,
    m: &Module,
    auto_regs: &[(SymbolId, ExprRef, SymbolId)],
    keywords: &FxHashSet<&'static str>,
    out: &mut impl std::io::Write,
) -> std::io::Result<Vec<ArgPin>> {
    let arg_to_reg: FxHashMap<_, _> = auto_regs.iter().map(|(reg, _, arg)| (*arg, *reg)).collect();

    let mut pins_by_name = FxHashMap::default();
    for (idx, p) in proto_methods(m).enumerate() {
        for (arg_idx, arg) in p.args.iter().enumerate() {
            let sym = &st[arg.symbol()];
            assert!(sym.is_arg());
            let output_reg = arg_to_reg.get(&arg.symbol()).cloned();
            pins_by_name
                .entry(sym.name().to_string())
                .or_insert_with(Vec::new)
                .push((idx, arg_idx, sym.tpe(), output_reg))
        }
    }

    let mut pins_by_name: Vec<_> = pins_by_name.into_iter().collect();
    pins_by_name.sort();
    let method_names: Vec<_> = proto_methods(m).map(|p| p.name.to_string()).collect();
    let mut arg_pins = vec![];
    for (name, mut pins) in pins_by_name {
        debug_assert!(!pins.is_empty());
        pins.sort();
        let all_same = pins
            .iter()
            .all(|(_, _, tpe, reg)| tpe == &pins[0].2 && reg == &pins[0].3);
        let full_names: Vec<_> = pins
            .iter()
            .map(|(idx, ..)| format!("{}.{name}", method_names[*idx]))
            .collect();
        if all_same {
            // avoid keyword clashes by prefixing method name
            let name = if keywords.contains(name.as_str()) {
                format!("{}_{name}", method_names[pins[0].0])
            } else {
                name
            };
            declare_pin(&name, &pins[0], &full_names.join(", "), out)?;
            let ids = pins
                .iter()
                .map(|&(method_idx, arg_idx, ..)| ArgId {
                    method_idx,
                    arg_idx,
                })
                .collect();
            arg_pins.push(ArgPin {
                ids,
                name: name.clone(),
                output_reg: pins[0].3,
            });
        } else {
            for pin in &pins {
                let name = format!("{}_{name}", method_names[pin.0]);
                let comment = format!("{}.{name}", method_names[pin.0]);
                declare_pin(&name, pin, &comment, out)?;
                arg_pins.push(ArgPin {
                    ids: vec![ArgId {
                        method_idx: pin.0,
                        arg_idx: pin.1,
                    }],
                    name,
                    output_reg: pin.3,
                });
            }
        }
    }
    Ok(arg_pins)
}

fn declare_pin(
    name: &str,
    pin: &(usize, usize, Type, Option<SymbolId>),
    comment: &str,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let dir = if pin.3.is_some() { "output" } else { "input" };
    writeln!(
        out,
        "  {dir} {} {name} ,  // {comment}",
        logic(pin.2.bitwidth())
    )?;
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
            logic(pin.bitwidth()),
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

fn dut_pin_binding(
    m: &Module,
    pg: &ProtoGraph,
    symbol_names: &mut SymbolNames,
    expr_names: &mut ExprNames,
) {
    for (pin_idx, pin) in m.pins.iter().enumerate() {
        let name = format!("{DUT_PREFIX}{}", pin.name());
        for symbols in &m.proto_pin_map {
            let sym = symbols[pin_idx];
            insert_symbol_name(sym, name.clone(), pg, symbol_names, expr_names);
        }
    }
}
