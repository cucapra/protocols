// Copyright 2025-26 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use protocols::frontend::Module;

/// Concatenates all the names of `struct`s (`Design`s) into one single string
pub fn collects_module_names(duts: &[Module]) -> String {
    let mut dut_names: Vec<String> = duts.iter().map(|d| d.name.clone()).collect();
    dut_names.sort();
    dut_names.join(", ")
}

pub struct Instance {
    pub name: String,
    #[allow(dead_code)]
    module: String,
    pub module_id: usize,
}

/// Takes the contents of the `-i` CLI flag and tries to find
pub fn parse_instance(duts: &[Module], arg: &str) -> Instance {
    let parts: Vec<&str> = arg.split(':').collect();
    match parts.as_slice() {
        // `module` is the name of the design
        // (In Verilog, "modules" are like interfaces and you have "instances"
        // (concrete instantiations, aka implementations) of the module)
        [inst, module] => {
            if let Some(module_id) = duts.iter().position(|d| &d.name == module) {
                Instance {
                    name: inst.to_string(),
                    module: module.to_string(),
                    module_id,
                }
            } else {
                panic!(
                    "Unknown design {module} for instance {inst}. Did you mean {}?",
                    collects_module_names(duts)
                );
            }
        }
        _ => panic!("unexpected instance argument: {arg}"),
    }
}
