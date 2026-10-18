pub mod bounded_lowering;
pub mod determinize;
pub mod driver_to_monitor;
pub mod edge_contract;
pub mod fork_reach;
pub mod graph_interpreter;
pub mod graphviz;
pub mod joint_automaton;
pub mod known_bits_analysis;
pub mod lowering;
pub mod meta_automaton;
pub mod meta_graphviz;
pub mod meta_timing;
pub mod propagate_assigns;
pub mod proto_graph;
pub mod reaching_defs;
pub mod simplify_monitor;
pub mod trace_lowering;
// TODO: add a function to transform AST to IR
// pub fn frontend(
//     ast : ast::Protocol
// ) -> ir::Protocol
