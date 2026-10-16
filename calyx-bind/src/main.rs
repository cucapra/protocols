use clap::{ColorChoice, Parser};
use patronus::expr::ExprRef;
use protocols::frontend;
use protocols::frontend::Module;
use protocols::frontend::ast::Protocol;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::SymbolTable;
use protocols::ir::graphviz::to_dot_string_from_entry;
use protocols::ir::lowering::{LoweredFragmentInfo, Lowerer};
use protocols::ir::proto_graph::{NodeId, Op, ProtoGraph};
use rustc_hash::FxHashSet;

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
    let (mut lowerer, lowered) = lower_protocols(st, m);
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
        .map(|(_, l)| get_single_cycle(&mut lowerer.ir, l).expect("reset should be single cycle"));
    let idle: Option<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_idle)
        .map(|(_, l)| get_single_cycle(&mut lowerer.ir, l).expect("idle should be single cycle"));

    // pad methods with idle to remove any forks in the protocol
    for (graph, method) in methods.iter().zip(m.protos.iter()) {
        remove_fork(&mut lowerer, graph, method, idle);
        // make sure it worked
        assert!(
            lowerer
                .graft_points(graph)
                .iter()
                .all(|(p, _)| *p == graph.exit)
        );
    }

    // generate unbounded driver
    let op_width = if methods.len() <= 1 {
        1
    } else {
        usize::BITS - (methods.len() - 1).leading_zeros()
    };

    for (graph, method) in methods.iter().zip(m.protos.iter()) {
        println!("{}", method.name);
        println!(
            "{}\n",
            to_dot_string_from_entry(&lowerer.ir, st, graph.entry)
        );
    }
}

/// returns the condition under which we will be done in the next step
fn next_state_is_done(pg: &mut ProtoGraph, node_id: NodeId) -> ExprRef {
    pg[node_id]
        .transitions
        .iter()
        .map(|t| {
            let done = pg[t.target]
                .actions
                .iter()
                .filter(|a| matches!(pg[a.op], Op::Done))
                .map(|a| a.guard)
                .fold(pg.false_id(), |a, b| pg.expr_ctx.or(a, b));
            pg.expr_ctx.and(done, t.guard)
        })
        .fold(pg.false_id(), |a, b| pg.expr_ctx.or(a, b))
}

fn remove_fork(
    lowerer: &mut Lowerer,
    graph: &LoweredFragmentInfo,
    method: &Protocol,
    idle: Option<NodeId>,
) {
    let mut todo = vec![(false, graph.entry)];
    let mut visited = FxHashSet::default();
    while let Some((mut has_forked, node_id)) = todo.pop() {
        if !visited.contains(&node_id) {
            // skip done nodes
            let is_done_state = lowerer.ir[node_id]
                .actions
                .iter()
                .find(|a| matches!(lowerer.ir[a.op], Op::Done))
                .is_some();
            if is_done_state {
                visited.insert(node_id);
                continue;
            }

            // check if this node forks
            let node_forks = try_remove_fork(&mut lowerer.ir, node_id);
            assert!(!(has_forked && node_forks), "Cannot fork twice");
            has_forked = has_forked | node_forks;
            if has_forked {
                let idle = idle.expect("an idle transaction is required because a protocol forks!");
                // parallel merge idle into state
                lowerer.graft_contracted_entry(node_id, idle, lowerer.ir.true_id());
            }

            for tran in &lowerer.ir[node_id].transitions {
                if tran.guard != lowerer.ir.false_id() && !visited.contains(&tran.target) {
                    assert!(tran.consumes_step);
                    todo.push((has_forked, tran.target));
                }
            }
            visited.insert(node_id);
        }
    }
}

fn try_remove_fork(pg: &mut ProtoGraph, node_id: NodeId) -> bool {
    let mut removed_fork = false;
    let mut actions = std::mem::take(&mut pg[node_id].actions);
    actions.retain(|a| {
        if matches!(pg[a.op], Op::Fork) {
            assert_eq!(a.guard, pg.true_id(), "guarded forks are not supported");
            assert!(!removed_fork, "double forks should have been merged");
            removed_fork = true;
            false
        } else {
            true
        }
    });
    pg[node_id].actions = actions;
    removed_fork
}

fn lower_protocols<'a>(st: &'a SymbolTable, m: &Module) -> (Lowerer<'a>, Vec<LoweredFragmentInfo>) {
    let mut lowerer = Lowerer::new(m.protos.first().unwrap().ctx.clone(), st);
    let lowered: Vec<_> = m
        .protos
        .iter()
        .map(|p| lowerer.lower_protocol_fragment(p, true, true))
        .collect();
    (lowerer, lowered)
}

fn get_single_cycle(pg: &mut ProtoGraph, low: &LoweredFragmentInfo) -> Option<NodeId> {
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
            // make a copy to remove the done state
            let mut st = pg[start_id].clone();
            st.transitions.clear();
            Some(pg.n(st))
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
