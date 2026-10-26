use crate::frontend::Module;
use crate::frontend::ast::Protocol;
use crate::frontend::symbol::SymbolTable;
use crate::ir::joint_automaton::{
    JointDriverError, JointTransitionKind, build_joint_control_automaton,
    joint_argument_substitutions, prepare_joint_protocols,
};
use crate::ir::lowering::Lowerer;
use crate::ir::proto_graph::{Action, Node, NodeId, Op, ProtoGraph, remap_expr};
use patronus::expr::{Context, ExprRef, TypeCheck};
use rustc_hash::FxHashMap;

/// An unbounded driver graph
pub struct JointDriverAutomaton {
    pub graph: ProtoGraph,
    pub protocols: Vec<Protocol>,
    pub choice_valid: ExprRef,
    pub protocol_choice: ExprRef,
    /// At each choice node, the logical tail slot for every protocol.
    pub choice_slots: FxHashMap<NodeId, Vec<usize>>,
    pub bank_counts: Vec<usize>,
}

/// Construct one finite automaton that can drive an unbounded, back-to-back
/// sequence of the supplied protocols.
/// The selected protocols must belong to `module`, whose pin map identifies
/// the symbols for each shared DUT input.
pub fn build_joint_driver_automaton(
    ctx: &mut Context,
    module: &Module,
    protocols: Vec<Protocol>,
    symbols: &SymbolTable,
) -> Result<JointDriverAutomaton, JointDriverError> {
    let sources = prepare_joint_protocols(ctx, &protocols, symbols)?;
    let control = build_joint_control_automaton(ctx, &protocols, &sources, symbols)?;
    // create the inputs used to start the next transaction.
    let choice_width = if protocols.len() <= 1 {
        1
    } else {
        usize::BITS - (protocols.len() - 1).leading_zeros()
    };

    // choice_valid indicates whether a protocol is offered at this choice.
    let choice_valid = ctx.bv_symbol("choice_valid", 1);
    let protocol_choice = ctx.bv_symbol("protocol_choice", choice_width);

    // launches[i] = choice_valid && protocol_choice == i
    let launches = (0..protocols.len())
        .map(|protocol| {
            let selected = if protocols.len() == 1 {
                ctx.get_true()
            } else {
                let width = protocol_choice.get_bv_type(ctx).unwrap();
                let value = ctx.bit_vec_val(protocol, width);
                ctx.equal(protocol_choice, value)
            };
            ctx.and(choice_valid, selected)
        })
        .collect::<Vec<_>>();
    let stop = ctx.not(choice_valid);

    // set up a lowering so we can use its helpful graph mutators (TODO: This is a bit janky)
    let mut lowerer = Lowerer::new(protocols[0].ctx.clone(), symbols);
    lowerer.ir = control.graph;

    // Assignments use SymbolId's on their LHS. Since each protocol has different SymbolIds for
    // the ports, we choose the first protocol and standardize on its symbols with the `target` map
    // TODO: is there a better way to do this
    let first = module
        .protos
        .iter()
        .position(|protocol| protocol.scope == protocols[0].scope)
        .expect("selected protocols must belong to the module");
    let targets = module
        .proto_pin_map
        .iter()
        .flat_map(|pins| pins.iter().zip(&module.proto_pin_map[first]))
        .filter_map(|(&symbol, &target)| symbols[symbol].is_in_port().then_some((symbol, target)))
        .collect::<FxHashMap<_, _>>();

    let nodes = lowerer.ir.nodes().map(|(id, _)| id).collect::<Vec<_>>();
    for node in nodes {
        for (index, edge) in lowerer.ir.node_mut(node).transitions.iter_mut().enumerate() {
            // and the transition guard with the driver-specific guard depending on its type
            let selection = match control.transition_kinds[&(node, index)] {
                JointTransitionKind::Launch(protocol) => launches[protocol],
                JointTransitionKind::Stop => stop,
                JointTransitionKind::Continue => ctx.get_true(),
            };
            edge.guard = ctx.and(edge.guard, selection);
        }

        // if this is a choice node, check if it has a done (this occurs when there is no
        // outstanding transactions). We then set the guard on the one to !choice_valid.
        if control.choice_slots.contains_key(&node) {
            debug_assert!(
                lowerer.ir[node]
                    .actions
                    .iter()
                    .all(|action| matches!(lowerer.ir[action.op], Op::Done))
            );
            for action in lowerer.ir.node_mut(node).actions.iter_mut() {
                // The control builder emits only global Done actions here.
                action.guard = stop;
            }
        }

        // actually fill in the node with the correct actions.
        lowerer.add_input_dont_care_assignments(ctx, &protocols[0], node);
        let mut choices = Vec::new();
        for instance in &control.instances[&node] {
            let source = &sources[instance.protocol];
            let substitutions = joint_argument_substitutions(
                ctx,
                source,
                &protocols[instance.protocol],
                symbols,
                instance.slot,
            );
            let mut actions = Vec::new();
            for action in &source[instance.control].actions {
                if matches!(source[action.op], Op::Fork | Op::Done) {
                    continue;
                }
                let op = source[action.op].remap(ctx, &substitutions, &targets);
                let op = lowerer.ir.o(op);
                let guard = remap_expr(ctx, action.guard, &substitutions);
                actions.push(Action::new(guard, op));
            }
            let copied = lowerer.ir.n(Node {
                actions,
                transitions: Vec::new(),
            });
            if instance.starts {
                choices.push((copied, launches[instance.protocol]));
            } else {
                Lowerer::graft_contracted_entry(
                    lowerer.symbols,
                    ctx,
                    &mut lowerer.ir,
                    node,
                    copied,
                    ctx.get_true(),
                );
            }
        }
        if !choices.is_empty() {
            lowerer.graft_disjoint_contracted_entries(ctx, node, &choices);
        }
    }
    lowerer.ir.garbage_collect_unreachable(ctx, false);
    lowerer.ir.simplify_all_exprs(ctx);
    Ok(JointDriverAutomaton {
        graph: lowerer.ir,
        protocols,
        choice_valid,
        protocol_choice,
        choice_slots: control.choice_slots,
        bank_counts: control.bank_counts,
    })
}
