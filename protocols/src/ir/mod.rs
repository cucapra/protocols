pub mod determinize;
pub mod edge_contract;
pub mod fork_reach;
pub mod graph_interpreter;
pub mod graphviz;
pub mod lowering;
pub mod propagate_assigns;
pub mod proto_graph;
pub mod reaching_defs;
pub mod trace_lowering;
// TODO: add a function to transform AST to IR
// pub fn frontend(
//     ast : ast::Protocol
// ) -> ir::Protocol
