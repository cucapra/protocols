// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::frontend::ast::{
    Ast, Clock, Expr, ExprId, Mapping, Protocol, ProtocolContext, RemapModule, Stmt, StmtId,
    find_symbols,
};
use crate::frontend::serialize::serialize_stmt;
use crate::frontend::symbol::{Arg, Field, StructId, SymbolId, SymbolKind, SymbolTable, Type};
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

pub fn to_modules(mut ast: Ast) -> (SymbolTable, Vec<Module>) {
    let mut modules = struct_to_modules(&ast.st, ast.protos);
    for remap in ast.remaps {
        debug_assert!(!modules.contains_key(&remap.name));
        let m = implement_remap(&mut ast.st, &modules, remap);
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

fn remapped_port(remap: &RemapModule, m: &Mapping) -> SymbolId {
    let rhs_syms: Vec<_> = find_symbols(&remap.ctx, m.rhs).into_iter().collect();
    let cond_syms: Vec<_> = find_symbols(&remap.ctx, m.cond).into_iter().collect();
    let mut all_syms: Vec<_> = rhs_syms.into_iter().chain(cond_syms).collect();
    all_syms.sort();
    all_syms.dedup();
    assert_eq!(all_syms.len(), 1);
    all_syms.into_iter().next().unwrap()
}

fn implement_remap(
    st: &mut SymbolTable,
    originals: &FxHashMap<String, Module>,
    remap: RemapModule,
) -> Module {
    let mut pins = vec![];
    let mut protos = vec![];
    let mut proto_pin_map = vec![];

    // create a struct for the remap module
    let remap_pins = remap
        .mappings
        .iter()
        .map(|m| Field::new(m.name.clone(), m.dir, m.tpe.clone()))
        .collect();
    let remap_struct_id = st.add_struct(remap.name.clone(), remap_pins);

    // pin to remap rule
    let pin_to_remap: FxHashMap<_, _> = remap
        .mappings
        .iter()
        .map(|m| {
            let sym = remapped_port(&remap, m);
            let name = st[sym].full_name(st);
            (name, (m, sym))
        })
        .collect();

    for impl_struct_id in &remap.implements {
        let orig_mod = &originals[st[impl_struct_id].name()];
        for (proto, pin_syms) in orig_mod.protos.iter().zip(orig_mod.proto_pin_map.iter()) {
            // create mappings lookup
            let lookup: FxHashMap<SymbolId, _> = orig_mod
                .pins
                .iter()
                .zip(pin_syms.iter())
                .map(|(field, sym)| {
                    let name = format!("{}.{}", orig_mod.name, field.name());
                    let mapping = pin_to_remap[&name];
                    (*sym, mapping)
                })
                .collect();

            protos.push(remap_proto(st, proto, remap_struct_id, &lookup, &remap.ctx));
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
    st: &'a mut SymbolTable,
    orig: &'a Protocol,
    lookup: &'a FxHashMap<SymbolId, (&'a Mapping, SymbolId)>,
    map_name_to_dut: FxHashMap<String, SymbolId>,
    remap_struct_id: StructId,
    remap_ctx: &'a ProtocolContext,
    out: Protocol,
}

fn remap_proto(
    st: &mut SymbolTable,
    orig: &Protocol,
    remap_struct_id: StructId,
    lookup: &FxHashMap<SymbolId, (&Mapping, SymbolId)>,
    remap_ctx: &ProtocolContext,
) -> Protocol {
    Remapper::new(st, orig, lookup, remap_struct_id, remap_ctx).run()
}

impl<'a> Remapper<'a> {
    fn new(
        st: &'a mut SymbolTable,
        orig: &'a Protocol,
        lookup: &'a FxHashMap<SymbolId, (&'a Mapping, SymbolId)>,
        remap_struct_id: StructId,
        remap_ctx: &'a ProtocolContext,
    ) -> Self {
        let mut out = Protocol::new(orig.name.clone(), orig.scope);

        // create a symbol table scope
        let scope_name = format!("{}::{}", st[remap_struct_id].name(), out.name);
        st.enter_scope(&scope_name);

        // create the type parameter
        let type_param_name = st[orig.type_param.unwrap()].name().to_string();
        let dut_sym = st.add_without_parent(
            type_param_name,
            Type::Struct(remap_struct_id),
            SymbolKind::Dut,
        );
        out.type_param = Some(dut_sym);
        let map_name_to_dut = st[remap_struct_id]
            .pins()
            .clone()
            .into_iter()
            .map(|pin| {
                let name = pin.name().to_string();
                let sym = st.add_with_parent(name.clone(), dut_sym);
                (name, sym)
            })
            .collect();

        // copy over arguments
        out.args = orig
            .args
            .iter()
            .map(|a| {
                let name = st[a.symbol()].name().to_string();
                let tpe = st[a.symbol()].tpe();
                let kind = st[a.symbol()].kind();
                let sym = st.add_without_parent(name, tpe, kind);
                Arg::new(sym)
            })
            .collect();

        Self {
            st,
            orig,
            out,
            lookup,
            remap_struct_id,
            map_name_to_dut,
            remap_ctx,
        }
    }
}

impl Remapper<'_> {
    fn run(mut self) -> Protocol {
        let body = self.on_stmt(self.orig.body);
        self.out.body = body;
        self.st.exit_scope();
        self.out
    }

    fn on_stmt(&mut self, stmt: StmtId) -> StmtId {
        println!("{}", serialize_stmt(self.orig, self.st, &stmt));
        match self.orig[stmt].clone() {
            Stmt::Block(inner) => {
                let inner = inner.into_iter().map(|s| self.on_stmt(s)).collect();
                self.out.s(Stmt::Block(inner))
            }
            Stmt::Assign(lhs, rhs) => {
                let rhs = self.on_expr(rhs);
                if let Some((m, map_sym_id)) = self.lookup.get(&lhs) {
                    let new_lhs = self.map_name_to_dut[&m.name];
                    let new_rhs = self.on_remap_expr(*map_sym_id, rhs, m.rhs);
                    self.out.s(Stmt::Assign(new_lhs, new_rhs))
                } else {
                    self.out.s(Stmt::Assign(lhs, rhs))
                }
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
            Expr::Sym(sym) => {
                let sym = self.st[sym].clone();
                match sym.kind() {
                    SymbolKind::Dut => unreachable!(),
                    SymbolKind::InPort => panic!("Did not expect to encounter an IN port!"),
                    SymbolKind::OutPort => {
                        todo!("Substitute out port")
                    }
                    SymbolKind::Arg(a_id) => {
                        let out_sym = self.out.args[a_id as usize].symbol();
                        self.out.e(Expr::Sym(out_sym))
                    }
                    SymbolKind::LoopVar => {
                        todo!("Substitute loop var")
                    }
                }
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

    /// We need to transform a remap expression to substitute the underlying port with
    /// the rhs from the original protocol.
    /// - in remap expr context: expr and port
    /// - in out expr context: rhs and return expression
    fn on_remap_expr(&mut self, port: SymbolId, rhs: ExprId, expr: ExprId) -> ExprId {
        match self.remap_ctx[expr].clone() {
            Expr::Const(a) => self.out.e(Expr::Const(a)),
            Expr::Sym(sym) if sym == port => rhs,
            Expr::Sym(_) => {
                todo!()
            }
            Expr::DontCare => self.out.dont_care_id(),
            Expr::Binary(op, a, b) => {
                let a = self.on_remap_expr(port, rhs, a);
                let b = self.on_remap_expr(port, rhs, b);
                self.out.e(Expr::Binary(op, a, b))
            }
            Expr::Unary(op, a) => {
                let a = self.on_remap_expr(port, rhs, a);
                self.out.e(Expr::Unary(op, a))
            }
            Expr::Slice(e, hi, lo) => {
                let e = self.on_remap_expr(port, rhs, e);
                self.out.e(Expr::Slice(e, hi, lo))
            }
            Expr::IsLastIteration => self.out.e(Expr::IsLastIteration),
            Expr::IterCount(v) => self.out.e(Expr::IterCount(v)),
        }
    }
}
