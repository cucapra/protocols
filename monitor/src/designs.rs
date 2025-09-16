// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use protocols::ir::{Field, SymbolId, SymbolTable, Transaction, Type};
use rustc_hash::FxHashMap;

/// Concatenates all the names of `struct`s (`Design`s) into one single string
pub fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<String> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
}

/// Metadata associated with a design (i.e. a `struct` in the Protocols language)
#[derive(Debug)]
#[allow(dead_code)]
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

#[allow(dead_code)]
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
        if let Some(symbol) = transaction.type_param {
            // We assume type parameters have to be structs
            let struct_id = match symbol_table[symbol].tpe() {
                Type::Struct(id) => id,
                o => panic!("Expect type parameter to always be a struct! But got: `{o:?}`"),
            };
            let name = symbol_table[struct_id].name().to_string();
            if let Some(design) = designs.get_mut(&name) {
                design.transaction_ids.push(transaction_id);
            } else {
                // `Field`s are also called `pin`s`
                let pins_vec: Vec<Field> = symbol_table[struct_id].pins().clone();

                // For each pin, look up its associated `SymbolId` in the symbol table
                let pins_with_ids: Vec<(SymbolId, Field)> = pins_vec
                    .into_iter()
                    .map(|pin| {
                        (
                            symbol_table
                                .symbol_id_from_name(pin.name())
                                .expect("Unable to find symbol ID for pin"),
                            pin,
                        )
                    })
                    .collect();
                designs.insert(
                    name.clone(),
                    Design {
                        name,
                        pins: pins_with_ids,
                        symbol_id: symbol,
                        transaction_ids: vec![transaction_id],
                    },
                );
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
