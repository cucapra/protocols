// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::frontend::ast::{Ast, Clock, Expr, ExprId, Protocol, RemapModule, Stmt, StmtId};
use crate::frontend::symbol::{Field, SymbolId, SymbolTable, Type};
use rustc_hash::FxHashMap;

/// Represents a DUT and associated protocols.
/// This could be the default `Module` created from a `struct`/`interface` or
/// a remapping from a protocol level `module` (internally referred to as [[RemapModule]]).
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub clock: Clock,
    pub pins: Vec<Field>,
    /// Protocols that use this struct
    pub protos: Vec<Protocol>,
    /// the symbols associated with the pins in the particular protocol.
    pub proto_pin_map: Vec<Vec<SymbolId>>,
}

pub fn to_modules(ast: Ast) -> (SymbolTable, Vec<Module>) {
    let mut modules = struct_to_modules(&ast.st, ast.protos);
    for remap in ast.remaps {
        debug_assert!(!modules.contains_key(&remap.name));
        let m = implement_remap(&ast.st, &modules, remap);
        modules.insert(m.name.clone(), m);
    }
    let mut out: Vec<_> = modules.into_values().collect();
    out.sort_by(|a, b| a.name.cmp(&b.name));
    (ast.st, out)
}

/// builds modules from `struct`/`interface`
fn struct_to_modules(st: &SymbolTable, protos: Vec<Protocol>) -> FxHashMap<String, Module> {
    let mut modules = FxHashMap::default();
    for proto in protos {
        if let Some(dut_symbol_id) = proto.type_param {
            // We assume type parameters have to be structs
            let struct_id = match st[dut_symbol_id].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let struct_name = st[struct_id].name().to_string();
            let module = modules
                .entry(struct_name.clone())
                .or_insert_with(|| Module {
                    name: struct_name.clone(),
                    clock: Clock::None,
                    pins: st[struct_id].pins().clone(),
                    protos: vec![],
                    proto_pin_map: vec![],
                });
            assert_eq!(module.name, struct_name);
            assert_eq!(&module.pins, st[struct_id].pins());

            // find the symbol id in this particular protocol mapping to the pins in the struct
            let pin_symbols = module
                .pins
                .iter()
                .map(|pin| {
                    st.symbol_id_from_name(
                        proto.scope,
                        &format!("{}.{}", st[dut_symbol_id].name(), pin.name()),
                    )
                    .unwrap_or_else(|| {
                        panic!(
                            "Unable to find symbol ID for pin {}, symbol_table is {}",
                            pin.name(),
                            st
                        )
                    })
                })
                .collect();
            module.proto_pin_map.push(pin_symbols);
            module.protos.push(proto);
        }
        // skipping any protocols that are not associated with a DUT
    }
    modules
}

fn implement_remap(
    st: &SymbolTable,
    originals: &FxHashMap<String, Module>,
    remap: RemapModule,
) -> Module {
    let mut pins = vec![];
    let mut protos = vec![];
    let mut proto_pin_map = vec![];
    for impl_struct_id in &remap.implements {
        let orig_mod = &originals[st[impl_struct_id].name()];
        for pin in &orig_mod.pins {}
        for proto in &orig_mod.protos {
            protos.push(remap_proto(st, proto));
        }
        println!("{}", orig_mod.name)
    }

    Module {
        name: remap.name,
        clock: remap.clock,
        pins,
        protos,
        proto_pin_map,
    }
}

struct Remapper<'a> {
    orig: &'a Protocol,
    out: Protocol,
}

fn remap_proto(st: &SymbolTable, orig: &Protocol) -> Protocol {
    Remapper::new(orig).run()
}

impl<'a> Remapper<'a> {
    fn new(orig: &'a Protocol) -> Self {
        let out = Protocol::new(orig.name.clone(), orig.scope);
        Self { orig, out }
    }
}

impl Remapper<'_> {
    fn run(mut self) -> Protocol {
        let body = self.on_stmt(self.orig.body);
        self.out.body = body;
        self.out
    }

    fn on_stmt(&mut self, stmt: StmtId) -> StmtId {
        match self.orig[stmt].clone() {
            Stmt::Block(inner) => {
                let inner = inner.into_iter().map(|s| self.on_stmt(s)).collect();
                self.out.s(Stmt::Block(inner))
            }
            Stmt::Assign(_, _) => {
                todo!()
            }
            Stmt::Step => self.out.s(Stmt::Step),
            Stmt::Fork => self.out.s(Stmt::Fork),
            Stmt::While(cond, body) => {
                let cond = self.on_expr(cond);
                let body = self.on_stmt(body);
                self.out.s(Stmt::While(cond, body))
            }
            Stmt::RepeatLoop(n, body) => {
                let n = self.on_expr(n);
                let body = self.on_stmt(body);
                self.out.s(Stmt::RepeatLoop(n, body))
            }
            Stmt::ForInLoop(loop_var, r, body) => {
                let r = self.on_expr(r);
                let body = self.on_stmt(body);
                self.out.s(Stmt::ForInLoop(loop_var, r, body))
            }
            Stmt::IfElse(cond, tru, fals) => {
                let cond = self.on_expr(cond);
                let tru = self.on_stmt(tru);
                let fals = self.on_stmt(fals);
                self.out.s(Stmt::IfElse(cond, tru, fals))
            }
            Stmt::AssertEq(l, r) => {
                let l = self.on_expr(l);
                let r = self.on_expr(r);
                self.out.s(Stmt::AssertEq(l, r))
            }
        }
    }

    fn on_expr(&mut self, expr: ExprId) -> ExprId {
        match self.orig[expr].clone() {
            Expr::Const(a) => self.out.e(Expr::Const(a)),
            Expr::Sym(_) => {
                todo!()
            }
            Expr::DontCare => self.out.dont_care_id(),
            Expr::Binary(op, a, b) => {
                let a = self.on_expr(a);
                let b = self.on_expr(b);
                self.out.e(Expr::Binary(op, a, b))
            }
            Expr::Unary(op, a) => {
                let a = self.on_expr(a);
                self.out.e(Expr::Unary(op, a))
            }
            Expr::Slice(e, hi, lo) => {
                let e = self.on_expr(e);
                self.out.e(Expr::Slice(e, hi, lo))
            }
            Expr::IsLastIteration => self.out.e(Expr::IsLastIteration),
            Expr::IterCount(v) => self.out.e(Expr::IterCount(v)),
        }
    }
}
