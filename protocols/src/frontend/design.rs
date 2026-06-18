// Copyright 2025-2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

//! # Design extraction
//! This module contains code to extract/infer Verilog designs from `struct` and protocol declarations.

use crate::frontend::ast::Protocol;
use crate::frontend::serialize::serialize_field;
use crate::frontend::symbol::{Field, SymbolId, SymbolTable, Type};
use anyhow::bail;
use rustc_hash::FxHashMap;

/// Metadata associated with a design (i.e. a `struct` in the Protocols language)
#[derive(Debug, Clone)]
pub struct Design {
    /// The name of the struct
    pub name: String,
    /// Pins from a struct
    pub pins: Vec<Field>,
    /// Index of protocols that use this struct + the symbols associated with the pins in the
    /// particular protocol.
    /// (e.g. an "Adder" supports these protocols)
    pub protocols: Vec<(usize, Vec<SymbolId>)>,
}

/// Pretty-prints a `Design` with respect to the current `SymbolTable`
pub fn serialize_design(symbol_table: &SymbolTable, design: &Design) -> String {
    let pins_str = design
        .pins
        .iter()
        .map(|field| serialize_field(symbol_table, field))
        .collect::<Vec<_>>()
        .join(",\n");
    format!(
        "Design {{\n\tname\n{}\npins: [\n{}\n]\nprotocol_ids: {:?}\n}}",
        design.name,
        pins_str,
        design
            .protocols
            .iter()
            .map(|(id, _)| *id)
            .collect::<Vec<_>>()
    )
}

/// Succeeds iff there is only a single `struct` with protocols in the file.
pub fn find_a_single_design(
    st: &SymbolTable,
    protos: &[Protocol],
    filename: &str,
) -> anyhow::Result<Design> {
    let designs = find_designs(&st, &protos);
    if designs.is_empty() {
        bail!("No protocols found in {}", filename);
    }
    if designs.len() > 1 {
        let design_names = designs.keys().cloned().collect::<Vec<_>>();
        bail!(
            "There are multiple structs in {}: {}.\nWe need to add a way to select which one we want to use.",
            filename,
            design_names.join(", ")
        );
    }
    Ok(designs.into_values().next().unwrap())
}

/// Finds all the protocols associated with a given `struct` (called a "design" since its a DUT),
/// returning a `HashMap` from struct names to the actual `Design`
pub fn find_designs(st: &SymbolTable, protos: &[Protocol]) -> FxHashMap<String, Design> {
    // Maps the name of the protocol to metadata about the struct (design)
    // We use `FxHashMap` because its a bit faster than the usual `HashMap`
    let mut designs: FxHashMap<String, Design> = FxHashMap::default();
    for (proto_id, proto) in protos.iter().enumerate() {
        if let Some(dut_symbol_id) = proto.type_param {
            // We assume type parameters have to be structs
            let struct_id = match st[dut_symbol_id].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let struct_name = st[struct_id].name().to_string();
            let design = designs
                .entry(struct_name.clone())
                .or_insert_with(|| Design {
                    name: struct_name.clone(),
                    pins: st[struct_id].pins().clone(),
                    protocols: vec![],
                });
            assert_eq!(design.name, struct_name);
            assert_eq!(&design.pins, st[struct_id].pins());

            // find the symbol id in this particular protocol mapping to the pins in the struct
            let pin_symbols = design
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
            design.protocols.push((proto_id, pin_symbols))
        }
        // skipping any protocols that are not associated with a DUT
    }
    designs
}
