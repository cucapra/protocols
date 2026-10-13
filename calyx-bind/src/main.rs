use clap::{ColorChoice, Parser};
use protocols::frontend;
use protocols::frontend::Module;
use protocols::frontend::ast::Protocol;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::edge_contract::contract_edges;
use protocols::ir::lowering::lower_ast_to_ir;
use protocols::ir::propagate_assigns::propagate_assignments;
use protocols::ir::proto_graph::{Node, Op, ProtoGraph};
use protocols::ir::reaching_defs::reaching_definitions;
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
    let methods: Vec<_> = m
        .protos
        .iter()
        .filter(|p| !p.is_idle && !p.is_reset)
        .map(|p| lower_single_protocol(st, p))
        .collect();
    let reset: Option<_> = m
        .protos
        .iter()
        .find(|p| p.is_reset)
        .map(|p| lower_single_protocol(st, p));
    let idle: Option<_> = m
        .protos
        .iter()
        .find(|p| p.is_idle)
        .map(|p| lower_single_protocol(st, p));
}

fn lower_single_protocol(st: &SymbolTable, proto: &Protocol) -> ProtoGraph {
    let mut pg = lower_ast_to_ir(proto.clone(), st);
    contract_edges(&mut pg, st);
    let rd = reaching_definitions(&mut pg, st);
    propagate_assignments(&mut pg, st, &rd);
    pg
}

fn get_single_cycle(pg: &ProtoGraph) -> Option<&Node> {
    let start = &pg[pg.entry];
    // check to make sure that the start node is the only node
    if let [next] = start.transitions.as_slice()
        && next.consumes_step
        && next.guard == pg.true_id()
    {
        let end = &pg[next.target];
        if end.transitions.is_empty()
            && let Some(done) = end.actions.iter().find(|a| pg[a.op] == Op::Done)
            && done.guard == pg.true_id()
        {
            Some(start)
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
