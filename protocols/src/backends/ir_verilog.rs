// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Verilog Monitors from Graph-based IR

use crate::frontend::Module;
use crate::frontend::symbol::{Dir, Field, SymbolId, SymbolKind, SymbolTable};
use crate::ir::joint_monitor::{InstanceParameter, JointMonitorAutomaton};
use crate::ir::proto_graph::{Action, NodeId, Op, ProtoGraph};
use baa::{BitVecOps, WidthInt};
use patronus::expr::{Context, Expr, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn monitor_to_verilog(
    ctx: &mut Context,
    _name: &str,
    m: &Module,
    st: &SymbolTable,
    monitor: &JointMonitorAutomaton,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let vgen = VerilogGen::new(st, m, monitor, monitor_pin_dir);

    vgen.registers(st, ctx, out)?;
    vgen.state_machine(st, ctx, out)?;

    Ok(())
}

/// for a monitor, both outputs and inputs of the dut are treated as inputs
fn monitor_pin_dir(_pin: &Field) -> Dir {
    Dir::In
}

struct VerilogGen {
    keywords: FxHashSet<&'static str>,
    pg: ProtoGraph,
    symbol_names: FxHashMap<SymbolId, String>,
    expr_names: FxHashMap<ExprRef, String>,
    state_labels: Vec<String>,
    state_reg: String,
    state_width: WidthInt,
    regs: Vec<(SymbolId, InstanceParameter, ExprRef)>,
    pins: Vec<(String, Dir, WidthInt)>,
}

const NEXT_PREFIX: &str = "next_";
const MONITOR_PREFIX: &str = "$monitor_";
const DUT_PREFIX: &str = "dut_";

impl VerilogGen {
    fn new(
        st: &SymbolTable,
        m: &Module,
        mon: &JointMonitorAutomaton,
        pin_dir: fn(&Field) -> Dir,
    ) -> Self {
        let pg = mon.control.graph.clone();
        let keywords = FxHashSet::from_iter(VERILOG_KEYWORDS.iter().cloned());

        let num_states = pg.nodes().count();
        let state_width = usize::BITS - num_states.leading_zeros();
        let mut state_labels: Vec<_> = (0..num_states).map(|ii| format!("ST_{ii}")).collect();
        state_labels[pg.entry.as_u32() as usize] = "ST_ENTRY".to_string();
        state_labels[mon.bad_state.as_u32() as usize] = "ST_BAD".to_string();
        let state_reg = "state".to_string();

        let mut regs: Vec<_> = mon
            .registers
            .iter()
            .map(|(k, v)| (*v, *k, mon.register_inits[v]))
            .collect();
        regs.sort();
        let pins: Vec<_> = m
            .pins
            .iter()
            .map(|p| {
                (
                    format!("{DUT_PREFIX}{}", p.name()),
                    pin_dir(p),
                    p.bitwidth(),
                )
            })
            .collect();

        let mut out = Self {
            keywords,
            symbol_names: FxHashMap::default(),
            expr_names: FxHashMap::default(),
            pg,
            state_labels,
            state_reg,
            state_width,
            regs: regs.clone(),
            pins: pins.clone(),
        };

        // compute Verilog compatible names for all automaton registers
        for &(reg, ..) in &regs {
            let reg_name = st[reg].name().to_string();
            if let Some(name) = reg_name.strip_prefix(MONITOR_PREFIX) {
                let new_name = format!("_{name}");
                out.insert_symbol_name(reg, new_name);
            }
        }

        // register dut pins
        for (pin_idx, (pin_name, ..)) in pins.into_iter().enumerate() {
            for syms in &m.proto_pin_map {
                let sym = syms[pin_idx];
                out.insert_symbol_name(sym, pin_name.clone());
            }
        }

        out
    }

    fn insert_symbol_name(&mut self, sym: SymbolId, name: String) {
        assert!(!self.keywords.contains(name.as_str()));
        let expr = self.pg.symbol_expr[&sym];
        self.symbol_names.insert(sym, name.clone());
        self.expr_names.insert(expr, name);
    }

    fn registers(
        &self,
        st: &SymbolTable,
        ctx: &Context,
        out: &mut impl std::io::Write,
    ) -> std::io::Result<()> {
        writeln!(out, "  typedef enum logic [{}:0] {{", self.state_width - 1)?;
        let entries: Vec<_> = self
            .state_labels
            .iter()
            .enumerate()
            .map(|(idx, lbl)| format!("    {lbl}  = {}'d{idx}", self.state_width))
            .collect();
        writeln!(out, "{}", entries.join(",\n"))?;
        writeln!(out, "  }} state_t;\n")?;
        writeln!(
            out,
            "  state_t {}, {NEXT_PREFIX}{};",
            self.state_reg, self.state_reg
        )?;
        for (reg, ..) in &self.regs {
            let name = &self.symbol_names[reg];
            writeln!(
                out,
                "  {} {}, {NEXT_PREFIX}{};",
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
            "      {} <= {};",
            self.state_reg,
            self.state_labels[self.pg.entry.as_u32() as usize]
        )?;
        for (reg, _, value) in &self.regs {
            writeln!(
                out,
                "      {} <= {};",
                self.symbol_names[reg],
                self.expr_to_verilog(ctx, *value)
            )?;
        }
        writeln!(out, "    end else begin",)?;
        writeln!(
            out,
            "      {} <= {NEXT_PREFIX}{};",
            self.state_reg, self.state_reg
        )?;
        for (reg, _, _) in &self.regs {
            let name = &self.symbol_names[reg];
            writeln!(out, "      {name} <= {NEXT_PREFIX}{name};",)?;
        }
        writeln!(out, "    end",)?;
        writeln!(out, "  end\n",)?;

        Ok(())
    }

    fn state_machine(
        &self,
        st: &SymbolTable,
        ctx: &Context,
        out: &mut impl std::io::Write,
    ) -> std::io::Result<()> {
        writeln!(out, "  always_comb begin")?;
        writeln!(out, "    // register default to their previous values")?;
        writeln!(out, "    next_state = state;")?;
        for (reg, _, _) in &self.regs {
            let name = &self.symbol_names[reg];
            writeln!(out, "    {NEXT_PREFIX}{name} = {name};",)?;
        }
        writeln!(out)?;
        writeln!(out, "    // default values for dut inputs")?;
        for (pin_name, pin_dir, pin_width) in &self.pins {
            if *pin_dir == Dir::Out {
                // TODO: we need to know all the symbols that this pin maps to
                writeln!(
                    out,
                    "    // TODO: find all the assignments to this particular pin for a better default assignment!"
                )?;
                writeln!(out, "    {pin_name} = {pin_width}'d0;",)?;
            }
        }
        writeln!(out)?;

        // states
        writeln!(out, "    unique case (state)")?;
        for (idx, lbl) in self.state_labels.iter().enumerate() {
            writeln!(out, "    {lbl}: begin")?;
            let node_id = NodeId::from_u32(idx as u32);
            for act in &self.pg[node_id].actions {
                self.action_to_verilog(ctx, st, act, "      ", out)?;
            }
            for tran in &self.pg[node_id].transitions {
                if tran.guard == ctx.get_false() || tran.target == node_id {
                    continue;
                }

                if tran.guard != ctx.get_true() {
                    writeln!(out, "      if ({})", self.expr_to_verilog(ctx, tran.guard))?;
                    write!(out, "  ")?;
                }

                writeln!(
                    out,
                    "      next_{} = {};",
                    self.state_reg,
                    self.state_labels[tran.target.as_u32() as usize]
                )?;
            }
            writeln!(out, "    end")?;
        }
        writeln!(out, "    endcase")?;

        writeln!(out, "  end")?;
        Ok(())
    }

    fn expr_to_verilog(&self, ctx: &Context, expr: ExprRef) -> String {
        patronus::expr::traversal::bottom_up(ctx, expr, |ctx, expr, children: &[String]| {
            if let Some(s) = self.expr_names.get(&expr) {
                s.to_string()
            } else {
                match &ctx[expr] {
                    Expr::BVSymbol { name, .. } => ctx[*name].to_string(),
                    Expr::BVLiteral(value) => format!(
                        "{}'b{}",
                        value.get(ctx).width(),
                        value.get(ctx).to_bit_str()
                    ),
                    Expr::BVNot(a, ..) => {
                        format!("~{}", maybe_parens(&children[0], &ctx[*a], &ctx[expr]))
                    }
                    Expr::BVAnd(a, b, ..) => format!(
                        "{} & {}",
                        maybe_parens(&children[0], &ctx[*a], &ctx[expr]),
                        maybe_parens(&children[1], &ctx[*b], &ctx[expr])
                    ),
                    Expr::BVOr(a, b, ..) => format!(
                        "{} | {}",
                        maybe_parens(&children[0], &ctx[*a], &ctx[expr]),
                        maybe_parens(&children[1], &ctx[*b], &ctx[expr])
                    ),
                    Expr::BVEqual(a, b, ..) => format!(
                        "{} == {}",
                        maybe_parens(&children[0], &ctx[*a], &ctx[expr]),
                        maybe_parens(&children[1], &ctx[*b], &ctx[expr])
                    ),
                    other => todo!("{:?}", other),
                }
            }
        })
    }

    fn action_to_verilog(
        &self,
        ctx: &Context,
        st: &SymbolTable,
        act: &Action,
        indent: &str,
        out: &mut impl std::io::Write,
    ) -> std::io::Result<()> {
        if matches!(&self.pg[act.op], Op::InternalAssertFalse) {
            writeln!(
                out,
                "{indent}// assert_false({})",
                self.expr_to_verilog(ctx, act.guard)
            )?;
            return Ok(()); // ignore internal asserts
        }
        if act.guard != ctx.get_true() {
            writeln!(out, "{indent}if ({})", self.expr_to_verilog(ctx, act.guard))?;
            write!(out, "  ")?; // extra indent
        }
        match &self.pg[act.op] {
            // ignore don't care
            Op::Assign(lhs, rhs) => {
                let lhs = self.lhs_symbol_name(st, *lhs);
                if rhs.dont_care == ctx.get_true() {
                    writeln!(out, "{indent}// {lhs} = DontCare")?;
                } else {
                    if rhs.concretes.len() == 1 {
                        writeln!(
                            out,
                            "{indent}{lhs} = {};",
                            self.expr_to_verilog(ctx, rhs.concretes[0].1)
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
                            let tg = self.expr_to_verilog(ctx, tg);
                            let fg = self.expr_to_verilog(ctx, fg);
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
                    self.expr_to_verilog(ctx, *a),
                    self.expr_to_verilog(ctx, *b)
                )?;
            }
            Op::Fork => unreachable!("all forks should be gone!"),
            Op::InternalAssertFalse => {}
            Op::Done => writeln!(out, "{indent}// WARN: ignoring done")?,
        }
        Ok(())
    }

    fn lhs_symbol_name(&self, st: &SymbolTable, sym: SymbolId) -> String {
        // all symbols that appear on the lhs should be defined in the name table
        let name = &self.symbol_names[&sym];
        let sym = &st[sym];
        if sym.kind() == SymbolKind::AutomatonState {
            // on the lhs, we want to refer to the next state
            format!("next_{name}")
        } else {
            name.to_string()
        }
    }
}

/// try to only add parenthesis if necessary
fn maybe_parens(s: &str, e: &Expr, parent: &Expr) -> String {
    match (e, parent) {
        // simple leaf node do not need parens
        (
            Expr::BVSymbol { .. }
            | Expr::ArraySymbol { .. }
            | Expr::BVLiteral(..)
            | Expr::BVNot(..),
            _,
        ) => s.to_string(),
        // if we have an op where the order does not matter
        (Expr::BVAnd(..), Expr::BVAnd(..))
        | (Expr::BVOr(..), Expr::BVOr(..))
        | (Expr::BVXor(..), Expr::BVXor(..)) => s.to_string(),
        _ => format!("({s})"),
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

/// Totally LLM generated _maybe_ Verilog keywords :cry:
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
