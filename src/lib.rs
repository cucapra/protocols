// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

pub mod diagnostic;
mod errors;
mod interface;
mod interpreter;
pub mod ir;
pub mod parser;
pub mod scheduler;
pub mod serialize;
pub mod typecheck;
mod yosys;
mod type_inference;