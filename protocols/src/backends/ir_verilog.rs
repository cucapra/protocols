// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Verilog Monitors from Graph-based IR

use crate::frontend::Module;
use crate::frontend::symbol::{Dir, Field, SymbolId, SymbolTable};
use crate::ir::joint_monitor::{InstanceParameter, JointMonitorAutomaton};
use crate::ir::proto_graph::ProtoGraph;
use baa::{BitVecOps, WidthInt};
use patronus::expr::{Context, Expr, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn monitor_to_verilog(
    ctx: &mut Context,
    name: &str,
    m: &Module,
    st: &SymbolTable,
    monitor: &JointMonitorAutomaton,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let vgen = VerilogGen::new(st, monitor, monitor_pin_dir);

    vgen.registers(st, ctx, out)?;

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
    pin_dir: fn(&Field) -> Dir,
}

const NEXT_PREFIX: &str = "next_";
const MONITOR_PREFIX: &str = "$monitor_";

impl VerilogGen {
    fn new(st: &SymbolTable, mon: &JointMonitorAutomaton, pin_dir: fn(&Field) -> Dir) -> Self {
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

        let mut out = Self {
            keywords,
            symbol_names: FxHashMap::default(),
            expr_names: FxHashMap::default(),
            pg,
            state_labels,
            state_reg,
            state_width,
            regs: regs.clone(),
            pin_dir,
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

        out
    }

    fn insert_symbol_name(&mut self, sym: SymbolId, name: String) {
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
        writeln!(out, "  state_t state, {NEXT_PREFIX}state;")?;
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
            "      state <= {};",
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
        writeln!(out, "      state <= {NEXT_PREFIX}state;",)?;
        for (reg, _, _) in &self.regs {
            let name = &self.symbol_names[reg];
            writeln!(out, "      {name} <= {NEXT_PREFIX}{name};",)?;
        }
        writeln!(out, "    end",)?;
        writeln!(out, "  end\n",)?;

        Ok(())
    }

    fn expr_to_verilog(&self, ctx: &Context, expr: ExprRef) -> String {
        patronus::expr::traversal::bottom_up(ctx, expr, |ctx, expr, children| {
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
                    Expr::BVNot(..) => format!("~({})", children[0]),
                    Expr::BVAnd(..) => format!("({}) & ({})", children[0], children[1]),
                    Expr::BVOr(..) => format!("({}) | ({})", children[0], children[1]),
                    Expr::BVEqual(..) => format!("({}) == ({})", children[0], children[1]),
                    other => todo!("{:?}", other),
                }
            }
        })
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
