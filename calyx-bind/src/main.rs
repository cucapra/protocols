use clap::{ColorChoice, Parser};
use protocols::frontend;
use protocols::frontend::Module;
use protocols::frontend::ast::Protocol;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::edge_contract::contract_edges;
use protocols::ir::lowering::{LoweredFragmentInfo, Lowerer, lower_ast_to_ir};
use protocols::ir::propagate_assigns::propagate_assignments;
use protocols::ir::proto_graph::{Node, NodeId, Op, ProtoGraph};
use protocols::ir::reaching_defs::reaching_definitions;
use rustc_hash::FxHashSet;
use std::any::Any;

#[derive(Parser, Debug)]
struct Args {
    #[arg(
        short,
        long,
        value_name = "PROTOCOLS_FILE",
        help = "One or several protocol files."
    )]
    protocol: Vec<String>,

    /// Allow arguments to appear in while/if conditions
    #[arg(long)]
    allow_branch_on_arg: bool,

    /// Paths to one or more Verilog (.v) files
    #[arg(long, value_delimiter = ' ', num_args = 1..)]
    verilog: Vec<String>,

    /// Name of the top-level module/struct to generate a binding for
    #[arg(short, long)]
    module: String,
}

fn gen_driver(st: &SymbolTable, m: &Module) {
    assert!(m.protos.iter().filter(|p| p.is_idle).count() <= 1);
    assert!(m.protos.iter().filter(|p| p.is_reset).count() <= 1);
    let (mut pg, lowered) = lower_protocols(st, m);
    debug_assert_eq!(lowered.len(), m.protos.len());
    let methods: Vec<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .filter(|(p, _)| !p.is_idle && !p.is_reset)
        .map(|(_, l)| l)
        .collect();
    let reset: Option<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_reset)
        .map(|(_, l)| get_single_cycle(&pg, l).expect("reset should be single cycle"));
    let idle: Option<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_idle)
        .map(|(_, l)| get_single_cycle(&pg, l).expect("idle should be single cycle"));

    // pad methods with idle
    for (graph, method) in methods.iter().zip(m.protos.iter()) {
        remove_fork(&mut pg, graph, method, idle);
    }

    println!("Reset: {reset:?}");
    println!("Idle: {idle:?}");
}

fn remove_fork(
    pg: &mut ProtoGraph,
    graph: &LoweredFragmentInfo,
    method: &Protocol,
    idle: Option<NodeId>,
) {
    println!("{}", method.name);
    let mut todo = vec![(false, graph.entry)];
    let mut visited = FxHashSet::default();
    while let Some((has_forked, node_id)) = todo.pop() {
        if !visited.contains(&node_id) {
            for action in &pg[node_id].actions {
                println!("{action:?}, {:?}", pg[action.op]);
            }
            for tran in &pg[node_id].transitions {
                if tran.guard != pg.false_id() {
                    assert!(tran.consumes_step);
                    todo.push((has_forked, tran.target));
                }
            }
            println!();
            visited.insert(node_id);
        }
    }
}

fn lower_protocols(st: &SymbolTable, m: &Module) -> (ProtoGraph, Vec<LoweredFragmentInfo>) {
    let mut lowerer = Lowerer::new(m.protos.first().unwrap().ctx.clone(), st);
    let lowered: Vec<_> = m
        .protos
        .iter()
        .map(|p| lowerer.lower_protocol_fragment(p, true, true))
        .collect();
    (lowerer.ir, lowered)
}

fn get_single_cycle(pg: &ProtoGraph, low: &LoweredFragmentInfo) -> Option<NodeId> {
    let start_id = low.entry;
    let end_id = low.exit;
    let start = &pg[start_id];
    // check to make sure that the start node is the only node
    if let [next] = start.transitions.as_slice()
        && next.consumes_step
        && next.guard == pg.true_id()
        && next.target == end_id
    {
        let end = &pg[next.target];
        if end.transitions.is_empty()
            && let Some(done) = end.actions.iter().find(|a| pg[a.op] == Op::Done)
            && done.guard == pg.true_id()
        {
            Some(start_id)
        } else {
            None
        }
    } else {
        None
    }
}

fn main() {
    // Parse CLI args
    let args = Args::parse();

    // we always parse and type check the protocol file
    let skip_static_step_fork_checks = false;
    let mut d = DiagnosticHandler::new(ColorChoice::Auto, false, true, false);
    let (st, modules) = frontend(
        &args.protocol,
        &mut d,
        skip_static_step_fork_checks,
        args.allow_branch_on_arg,
    )
    .unwrap();

    let available_modules: Vec<_> = modules.iter().map(|m| m.name.clone()).collect();
    let module = modules
        .iter()
        .find(|m| m.name == args.module)
        .unwrap_or_else(|| {
            panic!(
                "Module {} not found. Available modules: {}",
                args.module,
                available_modules.join(", ")
            )
        });

    gen_driver(&st, module);
}
