use clap::{ColorChoice, Parser};
use patronus::expr::{Context, ExprRef, SerializableIrNode, TypeCheck, simple_transform_expr};
use patronus::system::{Output, TransitionSystem};
use protocols::backends::transition_system::{
    lower_proto_graph_to_transition_system, replace_expr,
};
use protocols::frontend::Module;
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::{Dir, SymbolTable};
use protocols::ir::graphviz::{to_dot_string, to_dot_string_from_entry};
use protocols::ir::joint_automaton::analyze_shape;
use protocols::ir::lowering::{LoweredFragmentInfo, Lowerer};
use protocols::ir::propagate_assigns::reachable_node_ids;
use protocols::ir::proto_graph::{Node, NodeId, Op, ProtoGraph, Transition};
use protocols::{PortId, frontend};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::io::Write;

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
    let mut ctx = Context::default();
    let (mut lowerer, lowered) = lower_protocols(&mut ctx, st, m);
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
        .map(|(_, l)| {
            get_single_cycle(&mut ctx, &mut lowerer.ir, l).expect("reset should be single cycle")
        });
    let idle: Option<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_idle)
        .map(|(_, l)| {
            get_single_cycle(&mut ctx, &mut lowerer.ir, l).expect("idle should be single cycle")
        });

    // pad methods with idle to remove any forks in the protocol
    for (graph, method) in methods.iter().zip(m.protos.iter()) {
        remove_fork(&mut ctx, &mut lowerer, graph, idle);
        // make sure it worked
        assert!(
            lowerer
                .graft_points(&mut ctx, graph)
                .iter()
                .all(|(p, _)| *p == graph.exit)
        );

        // check shape
        lowerer.ir.entry = graph.entry;
        let shape = analyze_shape(&ctx, &lowerer.ir, method).unwrap();
        assert!(
            shape.fork.is_none(),
            "we should have removed all forks at this point!"
        );
        assert!(shape.post.is_empty());
        assert_eq!(shape.done, graph.exit);
    }

    // guard method starts with op == i && go and merge them into a single start state
    let op_width = std::cmp::max(1, usize::BITS - (methods.len() - 1).leading_zeros());
    let op = ctx.bv_symbol("op", op_width);
    let go = ctx.bv_symbol("go", 1);

    // common start state
    lowerer.ir.entry = lowerer.ir.n(Node::empty());
    let entry = lowerer.ir.entry;
    // self loop if go is low
    lowerer.ir[entry]
        .transitions
        .push(Transition::new(ctx.not(go), entry, true));

    // merge methods into start state
    for (idx, graph) in methods.iter().enumerate() {
        let idx = ctx.bit_vec_val(idx, op_width);
        let selected = ctx.equal(op, idx);
        let selected_and_go = and(&mut ctx, go, selected);
        lowerer.graft_contracted_entry(&mut ctx, entry, graph.entry, selected_and_go);
    }
    // not go means we are in idle
    if let Some(idle) = idle {
        let not_go = ctx.not(go);
        lowerer.graft_contracted_entry(&mut ctx, entry, idle, not_go);
    }

    // build one common done state from idle
    let done_state_id = lowerer.ir.n(Node::empty());
    lowerer.ir[done_state_id]
        .transitions
        .push(Transition::new(ctx.get_true(), entry, true));
    if let Some(idle) = idle {
        lowerer.ir[done_state_id].actions = lowerer.ir[idle].actions.clone();
    }
    remove_done(&mut ctx, &mut lowerer.ir, done_state_id);
    remove_dont_care(st, &mut ctx, &mut lowerer.ir);

    // compact graph
    let node_remap = lowerer.ir.garbage_collect_unreachable(&ctx);
    lowerer.ir.simplify_all_exprs(&mut ctx);

    let mut node_labels: Vec<String> = (0..lowerer.ir.nodes().count())
        .map(|i| format!("node_{i}"))
        .collect();
    node_labels[lowerer.ir.entry.as_u32() as usize] = "start".to_string();
    node_labels[node_remap[&done_state_id].as_u32() as usize] = "done".to_string();

    // show graph
    println!("{}", to_dot_string(&ctx, &lowerer.ir, st));

    //
    // // lower to transition system
    // let sys = to_transition_system(&mut ctx, m, lowerer.ir, st);
    //
    // println!("{}", sys.serialize_to_str(&ctx));

    let mut verilog = vec![];
    // TODO: we need to actually extract the reset actions!!!!
    let reset = reset.map(|node_id| node_remap[&node_id]);
    to_verilog(&ctx, m, reset, &lowerer.ir, st, &node_labels, &mut verilog).unwrap();
    println!("{}", std::str::from_utf8(verilog.as_slice()).unwrap())
}

fn to_verilog(
    ctx: &Context,
    m: &Module,
    reset: Option<NodeId>,
    pg: &ProtoGraph,
    st: &SymbolTable,
    node_labels: &[String],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let num_states = pg.nodes().count();
    assert_eq!(num_states, node_labels.len());
    let state_labels: Vec<_> = node_labels
        .iter()
        .map(|l| format!("ST_{}", l.to_uppercase()))
        .collect();
    let state_width = usize::BITS - num_states.leading_zeros();

    writeln!(out, "  typedef enum logic [{}:0] {{", state_width - 1)?;
    for (idx, lbl) in state_labels.iter().enumerate() {
        writeln!(out, "    {lbl}  = {state_width}'d{idx},")?;
    }
    writeln!(out, "  }} state_t;\n")?;
    writeln!(out, "  state_t state, next_state;\n")?;
    // state register
    writeln!(out, "  always_ff @(posedge clk)")?;
    writeln!(
        out,
        "    if reset state <= {};",
        state_labels[pg.entry.as_u32() as usize]
    )?;
    writeln!(out, "    else state <= next_state;\n",)?;

    // combinational
    writeln!(out, "  always_comb begin")?;
    writeln!(out, "    if reset begin")?;
    if let Some(reset) = reset {
        state_to_verilog(ctx, pg, "      ", &pg[reset], out)?;
    }
    writeln!(out, "    end")?;

    writeln!(out, "  end")?;

    Ok(())
}

fn state_to_verilog(
    ctx: &Context,
    pg: &ProtoGraph,
    indent: &str,
    node: &Node,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    for act in &node.actions {
        writeln!(out, "{indent}// {act:?}")?;
    }
    Ok(())
}

fn remove_dont_care(st: &SymbolTable, ctx: &mut Context, pg: &mut ProtoGraph) {
    for node in reachable_node_ids(ctx, pg, pg.entry) {
        let actions = pg[node].actions.clone();
        for act in actions {
            if let Op::Assign(sym, assign) = &mut pg[act.op] {
                if assign.concretes.is_empty() {
                    let width: u32 = st[*sym].tpe().bitwidth();
                    assign.concretes.push((assign.dont_care, ctx.zero(width)));
                } else if assign.dont_care != ctx.get_false() {
                    let guard = &mut assign.concretes[0].0;
                    *guard = ctx.or(*guard, assign.dont_care);
                }
                assign.dont_care = ctx.get_false();
            }
        }
    }
}

// node0 [label="[1] DUT.data_i := input if or(and(go, not(op)), not(or(op, not(go))))\n[1] DUT.v_i := 1; 0\n                                                [1] DUT.enq_not_deq_i := 1 if go; 0 if go\n[1] DUT.reset_i := 0\n[and(or(and(go, not(op)), and(go, op)), not(go))] internal_assert_false"];
// node0 [label="[1] DUT.data_i := X if or(op, not(go)); input if and(go, not(op))\n    [1] DUT.v_i := 1 if or(and(go, not(op)), and(go, op)); 0 if not(go)\n[1] DUT.enq_not_deq_i := X if not(go); 1 if and(go, not(op)); 0 if and(go, op)\n[1] DUT.reset_i := 0\n[and(or(and(go, not(op)), and(go, op)), not(go))] internal_assert_false"];

fn to_transition_system(
    ctx: &mut Context,
    module: &Module,
    pg: ProtoGraph,
    st: &SymbolTable,
) -> TransitionSystem {
    let mut sys = TransitionSystem::new(module.name.clone());
    let mut symbol_to_port = FxHashMap::default();
    let mut port_to_expr = FxHashMap::default();
    let mut port_to_dir = FxHashMap::default();
    // all DUT inputs are outputs, all DUT outputs are inputs
    for (pin_idx, pin) in module.pins.iter().enumerate() {
        let port = PortId::from_raw(pin_idx as u32);
        for syms in module.proto_pin_map.iter() {
            symbol_to_port.insert(syms[pin_idx], port);
        }
        let sym = ctx.bv_symbol(&format!("dut_{}", pin.name()), pin.bitwidth());
        if pin.dir() == Dir::Out {
            debug_assert_eq!(pin.dir(), Dir::Out);
            sys.inputs.push(sym);
        }
        port_to_dir.insert(port, pin.dir());
        port_to_expr.insert(port, sym);
    }

    let lowered = lower_proto_graph_to_transition_system(
        ctx,
        pg,
        sys,
        symbol_to_port,
        port_to_expr.clone(),
        st,
    );
    let mut sys = lowered.ts;

    for (port, &expr) in &lowered.port_to_expr {
        if port_to_dir[port] == Dir::In {
            let port = port_to_expr[port];
            let name = ctx[port].get_symbol_name_ref().unwrap();
            sys.outputs.push(Output { name, expr });
        }
    }

    // remove_dont_care_inputs(ctx, &mut sys);
    patronus::system::transform::simplify_expressions(ctx, &mut sys);
    sys
}

fn remove_dont_care_inputs(ctx: &mut Context, sys: &mut TransitionSystem) {
    let mut remap = FxHashMap::default();
    sys.inputs.retain(|&i| {
        if ctx.get_symbol_name(i).unwrap().starts_with("dont_care") {
            remap.insert(i, ctx.zero(i.get_bv_type(ctx).unwrap()));
            false
        } else {
            true
        }
    });

    sys.update_expressions(|expr| {
        Some(simple_transform_expr(
            ctx,
            expr,
            |_ctx, candidate, _children| remap.get(&candidate).cloned(),
        ))
    });
}

/// returns the condition under which we will be done in the next step
fn next_state_is_done(ctx: &mut Context, pg: &ProtoGraph, node_id: NodeId) -> ExprRef {
    let done_guards: SmallVec<[_; 2]> = pg[node_id]
        .transitions
        .iter()
        .filter(|t| is_done_state(ctx, pg, t.target))
        .map(|t| t.guard)
        .collect();
    reduce_or(ctx, done_guards.into_iter())
}

fn is_done_state(ctx: &mut Context, pg: &ProtoGraph, node_id: NodeId) -> bool {
    // we only support done guarded with true or false
    let dones: SmallVec<[_; 2]> = pg[node_id]
        .actions
        .iter()
        .filter(|a| matches!(pg[a.op], Op::Done))
        .map(|a| a.guard)
        .collect();

    let expr = reduce_or(ctx, dones.into_iter());
    assert!(expr == ctx.get_true() || expr == ctx.get_false());
    expr == ctx.get_true()
}

fn reduce_or(ctx: &mut Context, items: impl Iterator<Item = ExprRef>) -> ExprRef {
    items
        .into_iter()
        .fold(ctx.get_false(), |a, b| or(ctx, a, b))
}

/// optimizing or
fn or(ctx: &mut Context, a: ExprRef, b: ExprRef) -> ExprRef {
    if a == ctx.get_true() || b == ctx.get_true() {
        ctx.get_true()
    } else if b == ctx.get_false() {
        a
    } else if a == ctx.get_false() {
        b
    } else if a == b {
        a
    } else {
        ctx.or(a, b)
    }
}

/// optimizing and
fn and(ctx: &mut Context, a: ExprRef, b: ExprRef) -> ExprRef {
    if a == ctx.get_false() || b == ctx.get_false() {
        ctx.get_false()
    } else if b == ctx.get_true() {
        a
    } else if a == ctx.get_true() {
        b
    } else if a == b {
        a
    } else {
        ctx.and(a, b)
    }
}

fn remove_done(ctx: &mut Context, pg: &mut ProtoGraph, done_state_id: NodeId) {
    let mut todo = vec![pg.entry];
    let mut visited = FxHashSet::default();
    while let Some(node_id) = todo.pop() {
        if !visited.contains(&node_id) {
            visited.insert(node_id);
            let is_done_state: SmallVec<[_; 2]> = pg[node_id]
                .transitions
                .iter()
                .map(|t| is_done_state(ctx, pg, t.target))
                .collect();
            for (tran, next_is_done_state) in pg[node_id]
                .transitions
                .iter_mut()
                .zip(is_done_state.into_iter())
            {
                if next_is_done_state {
                    tran.target = done_state_id;
                } else if tran.guard != ctx.get_false() && !visited.contains(&tran.target) {
                    assert!(tran.consumes_step);
                    todo.push(tran.target);
                }
            }
        }
    }
}

fn remove_fork(
    ctx: &mut Context,
    lowerer: &mut Lowerer,
    graph: &LoweredFragmentInfo,
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
            let node_forks = try_remove_fork(ctx, &mut lowerer.ir, node_id);
            assert!(!(has_forked && node_forks), "Cannot fork twice");
            has_forked = has_forked | node_forks;
            if has_forked {
                let idle = idle.expect("an idle transaction is required because a protocol forks!");
                // parallel merge idle into state
                lowerer.graft_contracted_entry(ctx, node_id, idle, ctx.get_true());
            }

            for tran in &lowerer.ir[node_id].transitions {
                if tran.guard != ctx.get_false() && !visited.contains(&tran.target) {
                    assert!(tran.consumes_step);
                    todo.push((has_forked, tran.target));
                }
            }
            visited.insert(node_id);
        }
    }
}

fn try_remove_fork(ctx: &mut Context, pg: &mut ProtoGraph, node_id: NodeId) -> bool {
    let mut removed_fork = false;
    let mut actions = std::mem::take(&mut pg[node_id].actions);
    actions.retain(|a| {
        if matches!(pg[a.op], Op::Fork) {
            assert_eq!(a.guard, ctx.get_true(), "guarded forks are not supported");
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

fn lower_protocols<'a>(
    ctx: &mut Context,
    st: &'a SymbolTable,
    m: &Module,
) -> (Lowerer<'a>, Vec<LoweredFragmentInfo>) {
    let mut lowerer = Lowerer::new(m.protos.first().unwrap().ctx.clone(), st);
    let lowered: Vec<_> = m
        .protos
        .iter()
        .map(|p| lowerer.lower_protocol_fragment(ctx, p, true, true))
        .collect();
    (lowerer, lowered)
}

fn get_single_cycle(
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    low: &LoweredFragmentInfo,
) -> Option<NodeId> {
    // check to make sure that the start node is the only node
    let next_state_is_done = next_state_is_done(ctx, pg, low.entry);
    if next_state_is_done == ctx.get_true() {
        // make a copy to remove the done state
        let mut st = pg[low.entry].clone();
        st.transitions.clear();
        Some(pg.n(st))
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
