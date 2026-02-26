// Copyright 2025-2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

//! # Design extraction
//! This module contains code to extract/infer Verilog designs from `struct` and protocol declarations.

use crate::ir::{Field, SymbolId, SymbolTable, Transaction, Type};
use crate::serialize::serialize_field;
use log::info;
use rustc_hash::FxHashMap;

/// Metadata associated with a design (i.e. a `struct` in the Protocols language)
#[derive(Debug, Clone)]
pub struct Design {
    /// The name of the struct
    pub name: String,
    /// The `SymbolId` associated with the struct
    pub symbol_id: SymbolId,
    /// Pins from a struct, along with their associated `SymbolId`s
    pub pins: Vec<(SymbolId, Field)>,
    /// Index of transactions that use this struct
    /// (e.g. an "Adder" supports these transactions)
    pub transaction_ids: Vec<usize>,
}

/// Pretty-prints a `Design` with respect to the current `SymbolTable`
pub fn serialize_design(symbol_table: &SymbolTable, design: &Design) -> String {
    let symbol_str = format!(
        "symbol_id {} ({})",
        design.symbol_id,
        symbol_table[design.symbol_id].name()
    );
    let pins_str = design
        .pins
        .iter()
        .map(|(symbol_id, field)| {
            format!(
                "{} ({}) ↦ {}",
                symbol_table[symbol_id].full_name(symbol_table),
                symbol_id,
                serialize_field(symbol_table, field)
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");
    format!(
        "Design {{\n\tname: {}\n{}\npins: [\n{}\n]\ntransaction_ids: {:?}\n}}",
        design.name, symbol_str, pins_str, design.transaction_ids
    )
}

/// Finds all the protocols associated with a given `struct` (called a "design" since its a DUT),
/// returning a `HashMap` from struct names to the actual `Design`
pub fn find_designs<'a>(
    transactions: impl Iterator<Item = &'a (Transaction, SymbolTable)>,
) -> FxHashMap<String, Design> {
    // Maps the name of the transaction to metadata about the struct (design)
    // We use `FxHashMap` because its a bit faster than the usual `HashMap`
    let mut designs: FxHashMap<String, Design> = FxHashMap::default();
    for (transaction_id, (transaction, symbol_table)) in transactions.enumerate() {
        if let Some(dut_symbol_id) = transaction.type_param {
            // We assume type parameters have to be structs
            let struct_id = match symbol_table[dut_symbol_id].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let struct_name = symbol_table[struct_id].name().to_string();
            if let Some(design) = designs.get_mut(&struct_name) {
                design.transaction_ids.push(transaction_id);
            } else {
                // Extract all the fields from the struct
                // (`Field`s are also called `pin`s`)
                let pins_vec: Vec<Field> = symbol_table[struct_id].pins().clone();

                // For each pin, look up its associated `SymbolId` in the symbol table
                // This returns an association list mapping `SymbolId`s to their associated pins
                // Concretely, what we do is take each pin `p` and find
                // the `SymbolId` corresponding to `DUT.p`
                let pins_with_ids: Vec<(SymbolId, Field)> = pins_vec
                    .into_iter()
                    .map(|pin| {
                        (
                            symbol_table
                                .symbol_id_from_name(&format!(
                                    "{}.{}",
                                    symbol_table[dut_symbol_id].name(),
                                    pin.name()
                                ))
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Unable to find symbol ID for pin {}, symbol_table is {}",
                                        pin.name(),
                                        symbol_table
                                    )
                                }),
                            pin,
                        )
                    })
                    .collect();
                let design = Design {
                    name: struct_name.clone(),
                    pins: pins_with_ids,
                    symbol_id: dut_symbol_id,
                    transaction_ids: vec![transaction_id],
                };
                info!("Inserting {}", serialize_design(symbol_table, &design));
                designs.insert(struct_name, design);
            }
        }
        // skipping any transactions that are not associated with a DUT
    }
    designs
}
