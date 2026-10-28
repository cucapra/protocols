// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{SmallVecExprRef, op_port_width, proto_methods};
use baa::{BitVecOps, WidthInt};
use patronus::expr::{Context, Expr, ExprRef};
use protocols::frontend::Module;
use protocols::frontend::ast::Clock;
use protocols::frontend::symbol::{Dir, SymbolId, SymbolKind, SymbolTable, Type};
use protocols::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::smallvec;

const DUT_PREFIX: &str = "dut_";

fn insert_symbol_name(
    sym: SymbolId,
    name: String,
    pg: &ProtoGraph,
    symbol_names: &mut SymbolNames,
    expr_names: &mut ExprNames,
) {
    let expr = pg.symbol_expr[&sym];
    symbol_names.insert(sym, name.clone());
    expr_names.insert(expr, name);
}

#[allow(clippy::too_many_arguments)]
pub fn to_verilog(
    ctx: &mut Context,
    m: &Module,
    reset_actions: Vec<Action>,
    pg: &ProtoGraph,
    st: &SymbolTable,
    node_labels: &[String],
    auto_regs: &[(SymbolId, ExprRef, SymbolId)],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
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
    writeln!(out, "module {}Bind(", m.name)?;
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
            let arg_sym = proto_methods(m).skip(method_idx).next().unwrap().args[arg_idx].symbol();
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
            &symbol_names[reg],
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
            writeln!(out, "  assign {} = {};", pin.name, &symbol_names[&reg])?;
        }
    }
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
        .enumerate()
        .map(|(_, pin)| format!("{indent}  .{} ({DUT_PREFIX}{})", pin.name(), pin.name()))
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

fn logic(width: WidthInt) -> String {
    assert!(width > 0);
    if width == 1 {
        "logic".to_string()
    } else {
        format!("logic [{}:0]", width - 1)
    }
}

fn action_to_verilog(
    ctx: &Context,
    pg: &ProtoGraph,
    st: &SymbolTable,
    act: &Action,
    indent: &str,
    expr_names: &ExprNames,
    symbol_names: &SymbolNames,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    if act.guard != ctx.get_true() {
        writeln!(
            out,
            "{indent}if ({})",
            expr_to_verilog(ctx, act.guard, expr_names)
        )?;
        write!(out, "  ")?; // extra indent
    }
    match &pg[act.op] {
        // ignore don't care
        Op::Assign(lhs, rhs) => {
            let lhs = lhs_symbol_name(st, *lhs, symbol_names);
            if rhs.dont_care == ctx.get_true() {
                writeln!(out, "{indent}// {lhs} = DontCare")?;
            } else {
                if rhs.concretes.len() == 1 {
                    writeln!(
                        out,
                        "{indent}{lhs} = {};",
                        expr_to_verilog(ctx, rhs.concretes[0].1, expr_names)
                    )?;
                } else {
                    let false_assign = rhs
                        .concretes
                        .iter()
                        .find(|(_, e)| *e == ctx.get_false())
                        .cloned();
                    let true_assign = rhs
                        .concretes
                        .iter()
                        .find(|(_, e)| *e == ctx.get_true())
                        .cloned();
                    if let Some((tg, _)) = true_assign
                        && let Some((fg, _)) = false_assign
                        && rhs.concretes.len() == 2
                    {
                        let tg = expr_to_verilog(ctx, tg, expr_names);
                        let fg = expr_to_verilog(ctx, fg, expr_names);
                        if tg.len() < fg.len() {
                            writeln!(out, "{indent}{lhs} = {tg};")?;
                        } else {
                            writeln!(out, "{indent}{lhs} = ~({fg});")?;
                        }
                    } else {
                        todo!("deal with multiple options {rhs:?}")
                    }
                }
            }
        }
        Op::AssertEq(a, b) => {
            writeln!(
                out,
                "{indent}// TODO: assert_eq({}, {});",
                expr_to_verilog(ctx, *a, expr_names),
                expr_to_verilog(ctx, *b, expr_names)
            )?;
        }
        Op::Fork => unreachable!("all forks should be gone!"),
        Op::InternalAssertFalse => {}
        Op::Done => writeln!(out, "{indent}// WARN: ignoring done")?,
    }
    Ok(())
}

fn lhs_symbol_name(st: &SymbolTable, sym: SymbolId, symbol_names: &SymbolNames) -> String {
    // all symbols that appear on the lhs should be defined in the name table
    let name = &symbol_names[&sym];
    let sym = &st[sym];
    if sym.kind() == SymbolKind::AutomatonState {
        // on the lhs, we want to refer to the next state
        format!("next_{name}")
    } else {
        name.to_string()
    }
}

type SymbolNames = FxHashMap<SymbolId, String>;

type ExprNames = FxHashMap<ExprRef, String>;

fn expr_to_verilog(ctx: &Context, expr: ExprRef, expr_names: &ExprNames) -> String {
    patronus::expr::traversal::bottom_up(ctx, expr, |ctx, expr, children| {
        if let Some(s) = expr_names.get(&expr) {
            s.to_string()
        } else {
            match &ctx[expr] {
                Expr::BVSymbol { name, .. } => ctx[*name].to_string(),
                Expr::BVLiteral(value) => format!(
                    "{}'b{}",
                    value.get(ctx).width(),
                    value.get(ctx).to_bit_str()
                ),
                Expr::BVNot(..) => format!("~({})", children[0]),
                Expr::BVAnd(..) => format!("({}) & ({})", children[0], children[1]),
                Expr::BVOr(..) => format!("({}) | ({})", children[0], children[1]),
                Expr::BVEqual(..) => format!("({}) == ({})", children[0], children[1]),
                other => todo!("{:?}", other),
            }
        }
    })
}

/// Totally LLM generate :cry:
const VERILOG_KEYWORDS: &[&str] = &[
    "accept_on",
    "alias",
    "always",
    "always_comb",
    "always_ff",
    "always_latch",
    "and",
    "assert",
    "assign",
    "assume",
    "automatic",
    "before",
    "begin",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "buf",
    "bufif0",
    "bufif1",
    "byte",
    "case",
    "casex",
    "casez",
    "cell",
    "chandle",
    "checker",
    "class",
    "clocking",
    "cmos",
    "config",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "deassign",
    "default",
    "defparam",
    "design",
    "disable",
    "dist",
    "do",
    "edge",
    "else",
    "end",
    "endcase",
    "endchecker",
    "endclass",
    "endclocking",
    "endconfig",
    "endfunction",
    "endgenerate",
    "endgroup",
    "endinterface",
    "endmodule",
    "endpackage",
    "endprimitive",
    "endprogram",
    "endproperty",
    "endspecify",
    "endsequence",
    "endtable",
    "endtask",
    "enum",
    "event",
    "eventually",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "for",
    "force",
    "foreach",
    "forever",
    "fork",
    "forkjoin",
    "function",
    "generate",
    "genvar",
    "global",
    "highz0",
    "highz1",
    "if",
    "iff",
    "ifnone",
    "ignore_bins",
    "illegal_bins",
    "implements",
    "implies",
    "import",
    "incdir",
    "include",
    "initial",
    "inout",
    "input",
    "inside",
    "instance",
    "int",
    "integer",
    "interconnect",
    "interface",
    "intersect",
    "join",
    "join_any",
    "join_none",
    "large",
    "let",
    "liblist",
    "library",
    "local",
    "localparam",
    "logic",
    "longint",
    "macromodule",
    "matches",
    "medium",
    "modport",
    "module",
    "nand",
    "negedge",
    "nettype",
    "new",
    "nexttime",
    "nmos",
    "nor",
    "noshowcancelled",
    "not",
    "notif0",
    "notif1",
    "null",
    "or",
    "output",
    "package",
    "packed",
    "parameter",
    "pmos",
    "posedge",
    "primitive",
    "priority",
    "program",
    "property",
    "protected",
    "pull0",
    "pull1",
    "pulldown",
    "pullup",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "rcmos",
    "real",
    "realtime",
    "ref",
    "reg",
    "reject_on",
    "release",
    "repeat",
    "restrict",
    "return",
    "rnmos",
    "rpmos",
    "rtran",
    "rtranif0",
    "rtranif1",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "scalared",
    "sequence",
    "shortint",
    "shortreal",
    "showcancelled",
    "signed",
    "small",
    "soft",
    "solve",
    "specify",
    "specparam",
    "static",
    "string",
    "strong",
    "strong0",
    "strong1",
    "struct",
    "super",
    "supply0",
    "supply1",
    "sync_accept_on",
    "sync_reject_on",
    "table",
    "tagged",
    "task",
    "this",
    "throughout",
    "time",
    "timeprecision",
    "timeunit",
    "tran",
    "tranif0",
    "tranif1",
    "tri",
    "tri0",
    "tri1",
    "triand",
    "trior",
    "trireg",
    "type",
    "typedef",
    "union",
    "unique",
    "unique0",
    "unsigned",
    "until",
    "until_with",
    "untyped",
    "use",
    "uwire",
    "var",
    "vectored",
    "virtual",
    "void",
    "wait",
    "wait_order",
    "wand",
    "weak",
    "weak0",
    "weak1",
    "while",
    "wildcard",
    "wire",
    "with",
    "within",
    "wor",
    "xnor",
    "xor",
];
