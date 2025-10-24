// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

#![allow(dead_code)]

use log::info;
use protocols::{
    ir::{Field, Ident, SymbolId, SymbolTable, Transaction, Type},
    serialize::serialize_field,
};
use rustc_hash::FxHashMap;
use std::str::FromStr;

/// Concatenates all the names of `struct`s (`Design`s) into one single string
pub fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<String> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
}

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
        "Design {{\nname: {}\n{}\npins: [\n{}\n]\ntransaction_ids: {:?}\n}}",
        design.name, symbol_str, pins_str, design.transaction_ids
    )
}

impl Design {
    /// Takes a `pin_id` and retrieves the name of the corresponding `Field`
    /// (if one exists)
    pub fn get_pin_name(&self, pin_id: &SymbolId) -> Option<&str> {
        self.pins.iter().find_map(|(id, field)| {
            if id == pin_id {
                Some(field.name())
            } else {
                None
            }
        })
    }
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
        // Check whether the transaction is parameterized by a type parameter
        // of the form `<DUT: struct_type>`
        if let Some(struct_symbol_id) = transaction.type_param {
            // We assume type parameters have to be structs
            let struct_id = match symbol_table[struct_symbol_id].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let struct_name = symbol_table[struct_id].name().to_string();
            if let Some(design) = designs.get_mut(&struct_name) {
                design.transaction_ids.push(transaction_id);
            } else {
                // `Field`s are also called `pin`s`
                let pins_vec: Vec<Field> = symbol_table[struct_id].pins().clone();

                // For each pin, look up its associated `SymbolId` in the symbol table
                // We do this by calling `symbol_table.symbol_id_from_name(...)`
                // with the pin name, qualified by the name of the DUT
                // (i.e. when looking up the pin `a`, we call
                // `symbol_table.symbol_id_from_name(...)` on "DUT.a")
                let pins_with_ids: Vec<(SymbolId, Field)> = pins_vec
                    .into_iter()
                    .map(|pin| {
                        let qualified_name =
                            format!("{}.{}", symbol_table[struct_symbol_id].name(), pin.name());
                        info!("{}", qualified_name);
                        let ident = Ident::from_str(&qualified_name).unwrap_or_else(|_| {
                            panic!("Unable to convert {} to Ident", qualified_name)
                        });
                        (
                            symbol_table.lookup(&ident).unwrap_or_else(|| {
                                panic!(
                                    "Unable to find symbol ID for pin `{}`, symbol_table is {}",
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
                    symbol_id: struct_symbol_id,
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

/// Datatype representing an `Instance` of a `Design`
pub struct Instance {
    /// The name of the `Instance`
    pub name: String,

    /// The name of the `Design` that this `Instance` is implementing
    pub design_name: String,
}

/// Takes the contents of the `-i` CLI flag and tries to find an instance
pub fn parse_instance(duts: &FxHashMap<String, Design>, arg: &str) -> Instance {
    let parts: Vec<&str> = arg.split(':').collect();
    match parts.as_slice() {
        // (In Verilog, "modules" are like interfaces and you have "instances"
        // (concrete instantiations, aka implementations) of the module)
        [instance_name, module_name] => {
            if !duts.contains_key(*module_name) {
                panic!(
                    "Unknown design {module_name} for instance {instance_name}. Did you mean {}?",
                    collects_design_names(duts)
                );
            } else {
                Instance {
                    name: instance_name.to_string(),
                    design_name: module_name.to_string(),
                }
            }
        }
        _ => panic!("unexpected instance argument: {arg}"),
    }
}
