// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::frontend::ast::{Ast, Clock, Protocol, RemapModule};
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
    todo!()
}
