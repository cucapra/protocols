use baa::{BitVecOps, WidthInt};
use clap::{ColorChoice, Parser};
use patronus::expr::{Context, Expr, ExprRef};
use protocols::frontend;
use protocols::frontend::Module;
use protocols::frontend::ast::{Clock, Protocol};
use protocols::frontend::diagnostic::DiagnosticHandler;
use protocols::frontend::symbol::{Dir, SymbolId, SymbolKind, SymbolTable, Type};
use protocols::ir::driver_to_monitor::{MonitorAutomaton, convert_driver_to_capturing_driver};
use protocols::ir::graphviz::to_dot_string;
use protocols::ir::joint_automaton::analyze_shape;
use protocols::ir::lowering::Lowerer;
use protocols::ir::proto_graph::{Action, Node, NodeId, Op, ProtoGraph, Transition};
use protocols::ir::simplify_monitor::simplify_monitor;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};

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

fn proto_methods(m: &Module) -> impl Iterator<Item = &Protocol> {
    m.protos.iter().filter(|p| !p.is_idle && !p.is_reset)
}

fn gen_driver(st: &mut SymbolTable, m: &Module) {
    assert!(m.protos.iter().filter(|p| p.is_idle).count() <= 1);
    assert!(m.protos.iter().filter(|p| p.is_reset).count() <= 1);
    let mut ctx = Context::default();
    let (mut pg, lowered, auto_regs) = lower_protocols(st, &mut ctx, m);
    debug_assert_eq!(lowered.len(), m.protos.len());
    let methods: Vec<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .filter(|(p, _)| !p.is_idle && !p.is_reset)
        .map(|(_, l)| l)
        .collect();
    let reset_actions = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_reset)
        .map(|(_, l)| {
            let node_id =
                get_single_cycle(&mut ctx, &mut pg, *l).expect("reset should be single cycle");
            pg[node_id].actions.clone()
        })
        .unwrap_or_default();
    let idle: Option<_> = m
        .protos
        .iter()
        .zip(lowered.iter())
        .find(|(p, _)| p.is_idle)
        .map(|(_, l)| {
            get_single_cycle(&mut ctx, &mut pg, *l).expect("idle should be single cycle")
        });

    // pad methods with idle to remove any forks in the protocol
    for (&&entry_node, method) in methods.iter().zip(m.protos.iter()) {
        remove_fork(st, &mut ctx, &mut pg, entry_node, idle);

        // check shape
        pg.entry = entry_node;
        let shape = analyze_shape(&ctx, &pg, method).unwrap();
        assert!(
            shape.fork.is_none(),
            "we should have removed all forks at this point!"
        );
        assert!(shape.post.is_empty());
    }

    // guard method starts with op == i && go and merge them into a single start state
    let op = ctx.bv_symbol("op", op_port_width(m));
    let go = ctx.bv_symbol("go", 1);

    // common start state
    pg.entry = pg.n(Node::empty());
    let entry = pg.entry;
    // self loop if go is low
    pg[entry]
        .transitions
        .push(Transition::new(ctx.not(go), entry, true));

    // merge methods into start state
    for (idx, &&method_entry) in methods.iter().enumerate() {
        let idx = ctx.bit_vec_val(idx, op_port_width(m));
        let selected = ctx.equal(op, idx);
        let selected_and_go = and(&mut ctx, go, selected);
        Lowerer::graft_contracted_entry(
            st,
            &mut ctx,
            &mut pg,
            entry,
            method_entry,
            selected_and_go,
        );
    }

    // not go means we are in idle
    if let Some(idle) = idle {
        let not_go = ctx.not(go);
        Lowerer::graft_contracted_entry(&st, &mut ctx, &mut pg, entry, idle, not_go);
    }

    // build one common done state from idle
    let done_state_id = pg.n(Node::empty());
    pg[done_state_id]
        .transitions
        .push(Transition::new(ctx.get_true(), entry, true));
    if let Some(idle) = idle {
        pg[done_state_id].actions = pg[idle].actions.clone();
    }
    remove_done(&mut ctx, &mut pg, done_state_id);
    // remove_dont_care(st, &mut ctx, &mut pg);

    // compact graph
    let node_remap = pg.garbage_collect_unreachable(&ctx, true);
    let done_state_id = node_remap[&done_state_id];
    pg.simplify_all_exprs(&mut ctx);

    let mut node_labels: Vec<String> = (0..pg.nodes().count())
        .map(|i| format!("node_{i}"))
        .collect();
    node_labels[pg.entry.as_u32() as usize] = "start".to_string();
    node_labels[done_state_id.as_u32() as usize] = "done".to_string();

    // show graph
    println!("{}", to_dot_string(&ctx, &pg, st));

    let mut verilog = vec![];
    to_verilog(
        &ctx,
        m,
        reset_actions,
        &pg,
        st,
        &node_labels,
        &auto_regs,
        &mut verilog,
    )
    .unwrap();
    println!("{}", std::str::from_utf8(verilog.as_slice()).unwrap())
}

fn op_port_width(m: &Module) -> WidthInt {
    let num_methods = proto_methods(m).count();
    std::cmp::max(1, usize::BITS - (num_methods - 1).leading_zeros())
}

const DUT_PREFIX: &str = "dut_";

fn to_verilog(
    ctx: &Context,
    m: &Module,
    reset_actions: Vec<Action>,
    pg: &ProtoGraph,
    st: &SymbolTable,
    node_labels: &[String],
    auto_regs: &[(SymbolId, ExprRef, SymbolId)],
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    // module I/O
    writeln!(
        out,
        "// this file was generated from a protocol using calyx-bind"
    )?;
    writeln!(out, "module {}Bind(", m.name)?;
    writeln!(out, "  input  {} clk,   // global clock", logic(1))?;
    writeln!(
        out,
        "  input  {} reset, // 1-cycle active-high reset",
        logic(1)
    )?;
    writeln!(
        out,
        "  input  {} go,    // calyx standard control",
        logic(1)
    )?;
    writeln!(
        out,
        "  output {} done,  // calyx standard control",
        logic(1)
    )?;
    let ops: Vec<_> = proto_methods(m)
        .enumerate()
        .map(|(i, p)| format!("{i}={}", p.name))
        .collect();
    writeln!(
        out,
        "  input  {} op,    // {}",
        logic(op_port_width(m)),
        ops.join(", ")
    )?;
    let arg_pin_info = arg_pins(st, m, auto_regs, out)?;
    writeln!(out, ");\n")?;

    verilog_dut_instance(m, "  ", out)?;
    writeln!(out)?;

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
    writeln!(out, "  state_t state, next_state;")?;
    for (reg, value, _) in auto_regs {
        writeln!(
            out,
            "  {} {}, next_{};",
            logic(st[reg].tpe().bitwidth()),
            st[reg].name(),
            st[reg].name()
        )?;
    }
    writeln!(out)?;
    // registers
    writeln!(out, "  always_ff @(posedge clk) begin")?;
    writeln!(out, "    if reset begin",)?;
    writeln!(
        out,
        "      state <= {};",
        state_labels[pg.entry.as_u32() as usize]
    )?;
    for (reg, value, _) in auto_regs {
        writeln!(
            out,
            "      {} <= {};",
            st[reg].name(),
            expr_to_verilog(ctx, *value)
        )?;
    }
    writeln!(out, "    end else begin",)?;
    writeln!(out, "      state <= next_state;",)?;
    for (reg, _, _) in auto_regs {
        let name = st[reg].name();
        writeln!(out, "      {name} <= next_{name};",)?;
    }
    writeln!(out, "    end",)?;
    writeln!(out, "  end\n",)?;

    // connect output pins
    writeln!(
        out,
        "  // connect output arguments to registers that capture them"
    )?;
    for pin in &arg_pin_info {
        if let Some(reg) = pin.output_reg {
            writeln!(out, "  assign {} = {};", pin.name, st[reg].name())?;
        }
    }
    writeln!(out)?;

    // combinational
    writeln!(out, "  always_comb begin")?;
    writeln!(out, "    // register default to their previous values")?;
    writeln!(out, "    next_state = state;")?;
    for (reg, _, _) in auto_regs {
        let name = st[reg].name();
        writeln!(out, "    next_{name} = {name};",)?;
    }
    writeln!(out)?;
    writeln!(out, "    // default values for dut inputs")?;
    let assignments = assignment_expressions_by_target(pg);
    for pin in &m.pins {
        if pin.dir() == Dir::In {
            // TODO: we need to know all the symbols that this pin maps to
            writeln!(
                out,
                "    // TODO: find all the assignments to this particular pin for a better default assignment!"
            )?;
            writeln!(
                out,
                "    {DUT_PREFIX}{} = {}'d0;",
                pin.name(),
                pin.bitwidth()
            )?;
        }
    }
    writeln!(out)?;

    // reset
    writeln!(out, "    if reset begin")?;
    for act in &reset_actions {
        action_to_verilog(ctx, pg, st, act, "      ", out)?;
    }
    writeln!(out, "    end else begin")?;
    // states
    writeln!(out, "      case (state)")?;
    for (idx, lbl) in state_labels.iter().enumerate() {
        writeln!(out, "      {lbl}: begin")?;
        let node_id = NodeId::from_u32(idx as u32);
        for act in &pg[node_id].actions {
            action_to_verilog(ctx, pg, st, act, "        ", out)?;
        }
        for tran in &pg[node_id].transitions {
            if tran.guard == ctx.get_false() || tran.target == node_id {
                continue;
            }

            if tran.guard != ctx.get_true() {
                writeln!(out, "        if {}", expr_to_verilog(ctx, tran.guard))?;
                write!(out, "  ")?;
            }

            writeln!(
                out,
                "        state = {}",
                state_labels[tran.target.as_u32() as usize]
            )?;
        }
        writeln!(out, "      end")?;
    }
    writeln!(out, "      endcase")?;

    writeln!(out, "    end")?;

    writeln!(out, "  end")?;
    writeln!(out, "endmodule")?;

    Ok(())
}

fn assignment_expressions_by_target(pg: &ProtoGraph) -> FxHashMap<SymbolId, SmallVecExprRef> {
    let mut out = FxHashMap::default();
    for act in pg.nodes().flat_map(|(_, node)| node.actions.iter()) {
        if let Op::Assign(sym, assign) = &pg[act.op] {
            let vec = out.entry(*sym).or_insert_with(|| smallvec![]);
            for (_, expr) in &assign.concretes {
                vec.push(*expr);
            }
        }
    }
    out
}

#[derive(Debug)]
struct ArgPin {
    ids: Vec<ArgId>,
    name: String,
    output_reg: Option<SymbolId>,
}

#[derive(Debug)]
struct ArgId {
    method_idx: usize,
    arg_idx: usize,
}

fn arg_pins(
    st: &SymbolTable,
    m: &Module,
    auto_regs: &[(SymbolId, ExprRef, SymbolId)],
    out: &mut impl std::io::Write,
) -> std::io::Result<Vec<ArgPin>> {
    let arg_to_reg: FxHashMap<_, _> = auto_regs.iter().map(|(reg, _, arg)| (*arg, *reg)).collect();

    let mut pins_by_name = FxHashMap::default();
    for (idx, p) in proto_methods(m).enumerate() {
        for (arg_idx, arg) in p.args.iter().enumerate() {
            let sym = &st[arg.symbol()];
            assert!(sym.is_arg());
            let output_reg = arg_to_reg.get(&arg.symbol()).cloned();
            pins_by_name
                .entry(sym.name().to_string())
                .or_insert_with(|| vec![])
                .push((idx, arg_idx, sym.tpe(), output_reg))
        }
    }

    let mut pins_by_name: Vec<_> = pins_by_name.into_iter().collect();
    pins_by_name.sort();
    let method_names: Vec<_> = proto_methods(m).map(|p| p.name.to_string()).collect();
    let mut arg_pins = vec![];
    for (name, mut pins) in pins_by_name {
        debug_assert!(!pins.is_empty());
        pins.sort();
        let all_same = pins
            .iter()
            .all(|(_, _, tpe, reg)| tpe == &pins[0].2 && reg == &pins[0].3);
        let full_names: Vec<_> = pins
            .iter()
            .map(|(idx, ..)| format!("{}.{name}", method_names[*idx]))
            .collect();
        if all_same {
            declare_pin(&name, &pins[0], &full_names.join(", "), out)?;
            let ids = pins
                .iter()
                .map(|&(method_idx, arg_idx, ..)| ArgId {
                    method_idx,
                    arg_idx,
                })
                .collect();
            arg_pins.push(ArgPin {
                ids,
                name: name.clone(),
                output_reg: pins[0].3,
            });
        } else {
            for pin in &pins {
                let name = format!("{}_{name}", &method_names[pin.0]);
                let comment = format!("{}.{name}", &method_names[pin.0]);
                declare_pin(&name, pin, &comment, out)?;
                arg_pins.push(ArgPin {
                    ids: vec![ArgId {
                        method_idx: pin.0,
                        arg_idx: pin.1,
                    }],
                    name,
                    output_reg: pin.3,
                });
            }
        }
    }
    Ok(arg_pins)
}

fn declare_pin(
    name: &str,
    pin: &(usize, usize, Type, Option<SymbolId>),
    comment: &str,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    let dir = if pin.3.is_some() { "output" } else { "input" };
    writeln!(
        out,
        "  {dir} {} {name} ,  // {comment}",
        logic(pin.2.bitwidth())
    )?;
    Ok(())
}

fn verilog_dut_instance(
    m: &Module,
    indent: &str,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    // declare I/O
    for pin in &m.pins {
        writeln!(
            out,
            "{indent}{} {DUT_PREFIX}{}; // {:?}",
            logic(pin.bitwidth()),
            pin.name(),
            pin.dir()
        )?;
    }
    writeln!(out)?;

    // create module instance
    writeln!(out, "{indent}{} {}_inst (", m.name, m.name)?;
    // TODO: clock
    for pin in &m.pins {
        writeln!(
            out,
            "{indent}  .{} ({DUT_PREFIX}{}),",
            pin.name(),
            pin.name()
        )?;
    }

    Ok(())
}

fn logic(width: WidthInt) -> String {
    assert!(width > 0);
    if width == 1 {
        "logic".to_string()
    } else {
        format!("logic [{}:0]", width - 1)
    }
}

fn action_to_verilog(
    ctx: &Context,
    pg: &ProtoGraph,
    st: &SymbolTable,
    act: &Action,
    indent: &str,
    out: &mut impl std::io::Write,
) -> std::io::Result<()> {
    if act.guard != ctx.get_true() {
        writeln!(out, "{indent}if {}", expr_to_verilog(ctx, act.guard))?;
        write!(out, "  ")?; // extra indent
    }
    match &pg[act.op] {
        // ignore don't care
        Op::Assign(lhs, rhs) => {
            let lhs = lhs_symbol_name(st, *lhs);
            if rhs.dont_care == ctx.get_true() {
                writeln!(out, "{indent}// {lhs} = DontCare")?;
            } else {
                if rhs.concretes.len() == 1 {
                    writeln!(
                        out,
                        "{indent}{lhs} = {};",
                        expr_to_verilog(ctx, rhs.concretes[0].1)
                    )?;
                } else {
                    let false_assign = rhs
                        .concretes
                        .iter()
                        .find(|(_, e)| *e == ctx.get_false())
                        .cloned();
                    let true_assign = rhs
                        .concretes
                        .iter()
                        .find(|(_, e)| *e == ctx.get_true())
                        .cloned();
                    if let Some((tg, _)) = true_assign
                        && let Some((fg, _)) = false_assign
                        && rhs.concretes.len() == 2
                    {
                        let tg = expr_to_verilog(ctx, tg);
                        let fg = expr_to_verilog(ctx, fg);
                        if tg.len() < fg.len() {
                            writeln!(out, "{indent}{lhs} = {tg};")?;
                        } else {
                            writeln!(out, "{indent}{lhs} = ~({fg});")?;
                        }
                    } else {
                        todo!("deal with multiple options")
                    }
                }
            }
        }
        Op::AssertEq(a, b) => {
            writeln!(
                out,
                "{indent}// TODO: assert_eq({}, {});",
                expr_to_verilog(ctx, *a),
                expr_to_verilog(ctx, *b)
            )?;
        }
        Op::Fork => unreachable!("all forks should be gone!"),
        Op::InternalAssertFalse => {}
        Op::Done => writeln!(out, "{indent}// WARN: ignoring done")?,
    }
    Ok(())
}

fn lhs_symbol_name(st: &SymbolTable, sym: SymbolId) -> String {
    let sym = &st[sym];
    match sym.kind() {
        SymbolKind::Dut => panic!("unexpected DUT symbol!"),
        SymbolKind::InPort | SymbolKind::OutPort => format!("dut_{}", sym.name()),
        // TODO: find out what protocol the argument is for
        SymbolKind::Arg(_) => sym.name().to_string(),
        SymbolKind::LoopVar => todo!("loop var"),
        SymbolKind::AutomatonState => format!("next_{}", sym.name()),
    }
}

fn expr_to_verilog(ctx: &Context, expr: ExprRef) -> String {
    patronus::expr::traversal::bottom_up(ctx, expr, |ctx, expr, children| match &ctx[expr] {
        Expr::BVSymbol { name, .. } => ctx[*name].to_string(),
        Expr::BVLiteral(value) => format!(
            "{}'b{}",
            value.get(ctx).width(),
            value.get(ctx).to_bit_str()
        ),
        Expr::BVNot(..) => format!("~({})", children[0]),
        Expr::BVAnd(..) => format!("({}) & ({})", children[0], children[1]),
        Expr::BVOr(..) => format!("({}) | ({})", children[0], children[1]),
        other => todo!("{:?}", other),
    })
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
    st: &SymbolTable,
    ctx: &mut Context,
    pg: &mut ProtoGraph,
    entry: NodeId,
    idle: Option<NodeId>,
) {
    let mut todo = vec![(false, entry)];
    let mut visited = FxHashSet::default();
    while let Some((mut has_forked, node_id)) = todo.pop() {
        if !visited.contains(&node_id) {
            // skip done nodes
            let is_done_state = pg[node_id]
                .actions
                .iter()
                .find(|a| matches!(pg[a.op], Op::Done))
                .is_some();
            if is_done_state {
                visited.insert(node_id);
                continue;
            }

            // check if this node forks
            let node_forks = try_remove_fork(ctx, pg, node_id);
            assert!(!(has_forked && node_forks), "Cannot fork twice");
            has_forked = has_forked | node_forks;
            if has_forked {
                let idle = idle.expect("an idle transaction is required because a protocol forks!");
                // parallel merge idle into state
                Lowerer::graft_contracted_entry(st, ctx, pg, node_id, idle, ctx.get_true());
            }

            for tran in &pg[node_id].transitions {
                if tran.guard != ctx.get_false() && !visited.contains(&tran.target) {
                    assert!(tran.consumes_step);
                    todo.push((has_forked, tran.target));
                }
            }
            visited.insert(node_id);
        }
    }
}

type SmallVecExprRef = SmallVec<[ExprRef; 4]>;

fn assignment_targets(pg: &ProtoGraph) -> FxHashSet<SymbolId> {
    pg.nodes()
        .flat_map(|(_, node)| node.actions.iter())
        .filter_map(|action| match &pg[action.op] {
            Op::Assign(target, _) => Some(*target),
            _ => None,
        })
        .collect()
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

fn lower_protocols(
    st: &mut SymbolTable,
    ctx: &mut Context,
    m: &Module,
) -> (ProtoGraph, Vec<NodeId>, Vec<(SymbolId, ExprRef, SymbolId)>) {
    let mut graph = ProtoGraph::new(m.protos[0].ctx.clone());
    let mut regs_and_init = vec![];
    let autos = m.protos.iter().map(|p| {
        // println!("{}", p.name);
        let p = lower_proto(st, ctx, p);
        let assigned = assignment_targets(&p.graph);

        for (src, reg) in p.value_registers.iter().chain(p.knownness_registers.iter()) {
            if assigned.contains(reg) {
                // only collect if register is actually used!
                let init = p.register_inits[reg];
                regs_and_init.push((*reg, init, *src));
            }
        }
        p
    });
    let nodes: Vec<_> = autos
        .into_iter()
        .map(|a| add_to_graph(&mut graph, &a.graph))
        .collect();
    regs_and_init.sort();
    (graph, nodes, regs_and_init)
}

fn add_to_graph(pg: &mut ProtoGraph, other: &ProtoGraph) -> NodeId {
    let mut node_remap = FxHashMap::default();
    let mut op_remap = FxHashMap::default();
    let mut todo = vec![other.entry];
    while let Some(node) = todo.pop() {
        node_remap.entry(node).or_insert_with(|| {
            // copy over ops
            let mut actions = other[node].actions.clone();
            for act in actions.iter_mut() {
                act.op = *op_remap
                    .entry(act.op)
                    .or_insert_with(|| pg.o(other[act.op].clone()));
            }
            pg.n(Node {
                actions,
                transitions: vec![],
            })
        });
        for t in &other[node].transitions {
            if !node_remap.contains_key(&t.target) {
                todo.push(t.target);
            }
        }
    }

    for (&old_node, &repl_node) in &node_remap {
        pg[repl_node].transitions = other[old_node]
            .transitions
            .iter()
            .map(|t| Transition {
                guard: t.guard,
                target: node_remap[&t.target],
                consumes_step: t.consumes_step,
                rotations: t.rotations.clone(),
            })
            .collect();
    }
    node_remap[&other.entry]
}

fn lower_proto(st: &mut SymbolTable, ctx: &mut Context, p: &Protocol) -> MonitorAutomaton {
    let mut lowerer = Lowerer::new(p.ctx.clone(), st);
    let fragment = lowerer.lower_protocol_fragment(ctx, p, true, false);
    lowerer.postprocess_trace_fragment(ctx, &fragment);
    lowerer.ir.entry = fragment.entry;
    lowerer.ir.garbage_collect_unreachable(ctx, false);
    let auto = convert_driver_to_capturing_driver(ctx, lowerer.ir, st).unwrap();
    let auto = simplify_monitor(ctx, auto, st);
    auto
}

fn get_single_cycle(ctx: &mut Context, pg: &mut ProtoGraph, entry: NodeId) -> Option<NodeId> {
    // check to make sure that the start node is the only node
    let next_state_is_done = next_state_is_done(ctx, pg, entry);
    if next_state_is_done == ctx.get_true() {
        // make a copy to remove the done state
        let mut st = pg[entry].clone();
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
    let (mut st, modules) = frontend(
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

    gen_driver(&mut st, module);
}
