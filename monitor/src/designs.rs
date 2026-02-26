// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use rustc_hash::FxHashMap;
use protocols::design::Design;

/// Concatenates all the names of `struct`s (`Design`s) into one single string
pub fn collects_design_names(duts: &FxHashMap<String, Design>) -> String {
    let mut dut_names: Vec<String> = duts.keys().cloned().collect();
    dut_names.sort();
    dut_names.join(", ")
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
