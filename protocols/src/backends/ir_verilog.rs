// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Verilog Monitors from Graph-based IR

use crate::frontend::Module;
use crate::frontend::symbol::{SymbolId, SymbolTable};
use crate::ir::joint_monitor::{InstanceParameter, JointMonitorAutomaton};
use crate::ir::proto_graph::ProtoGraph;
use baa::WidthInt;
use patronus::expr::{Context, ExprRef};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn monitor_to_verilog(
    ctx: &mut Context,
    name: &str,
    m: &Module,
    st: &SymbolTable,
    monitor: &JointMonitorAutomaton,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let vgen = VerilogGen::new(
        monitor.control.graph.clone(),
        st,
        &monitor.registers,
        &monitor.register_inits,
    );

    todo!();

    Ok(())
}

struct VerilogGen {
    keywords: FxHashSet<&'static str>,
    pg: ProtoGraph,
    symbol_names: FxHashMap<SymbolId, String>,
    expr_names: FxHashMap<ExprRef, String>,
}

impl VerilogGen {
    fn new(
        pg: ProtoGraph,
        st: &SymbolTable,
        regs: &FxHashMap<InstanceParameter, SymbolId>,
        reg_inits: &FxHashMap<SymbolId, ExprRef>,
    ) -> Self {
        let keywords = FxHashSet::from_iter(VERILOG_KEYWORDS.iter().cloned());

        let mut out = Self {
            keywords,
            symbol_names: FxHashMap::default(),
            expr_names: FxHashMap::default(),
            pg,
        };

        // compute Verilog compatible names for all automaton registers
        let mut regs: Vec<_> = regs.iter().map(|(k, v)| (*v, *k, reg_inits[v])).collect();
        regs.sort();
        for &(reg, ..) in &regs {
            let reg_name = st[reg].name().to_string();
            if let Some(name) = reg_name.strip_prefix("$monitor_") {
                let new_name = format!("_{name}");
                out.insert_symbol_name(reg, new_name);
            }
        }

        out
    }

    fn insert_symbol_name(&mut self, sym: SymbolId, name: String) {
        let expr = self.pg.symbol_expr[&sym];
        self.symbol_names.insert(sym, name.clone());
        self.expr_names.insert(expr, name);
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
