use crate::ir::determinize::{SatResult, check_sat};
use crate::ir::propagate_assigns::reachable_node_ids;
use crate::ir::proto_graph::{NodeId, Op, ProtoGraph};
use crate::ir::reaching_defs::{predecessors, restrict_branch_to_edge, simplify_guard};
use itertools::Itertools;
use patronus::expr::ExprRef;
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForkReachability {
    Unreachable,
    DefinitelyNotForked,
    MaybeForked,
    DefinitelyForked,
}

#[derive(Debug, Default)]
pub struct ForkReach {
    pub in_reach: FxHashMap<NodeId, ForkReachability>,
    pub out_reach: FxHashMap<NodeId, ForkReachability>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ForkFact {
    // if `no_fork_guard` is true, there is a path where no fork was triggered
    // if `fork_guard` is true, there is a path where a fork was triggered
    no_fork_guard: ExprRef,
    fork_guard: ExprRef,
}

impl ForkFact {
    fn bottom(pg: &ProtoGraph) -> Self {
        Self {
            no_fork_guard: pg.false_id(),
            fork_guard: pg.false_id(),
        }
    }

    fn initial(pg: &ProtoGraph) -> Self {
        Self {
            // initially, we know there is a path where no fork was triggered (the trivial path)
            no_fork_guard: pg.true_id(),
            fork_guard: pg.false_id(),
        }
    }

    fn merge(pg: &mut ProtoGraph, lhs: Self, rhs: Self) -> Self {
        // merge all the paths where no fork was taken with OR, likewise for the fork taken paths
        let no_fork_guard = pg.or_guard(lhs.no_fork_guard, rhs.no_fork_guard);
        let fork_guard = pg.or_guard(lhs.fork_guard, rhs.fork_guard);
        Self {
            no_fork_guard: simplify_guard(pg, no_fork_guard),
            fork_guard: simplify_guard(pg, fork_guard),
        }
    }

    fn transfer(self, pg: &mut ProtoGraph, local_fork_guard: ExprRef) -> Self {
        // no fork is taken *out of* this node if into this path, the no_fork_guard is true AND the fork in this node was not triggered
        let not_local_fork = pg.not_guard(local_fork_guard);
        let no_fork_guard = pg.and_guard(self.no_fork_guard, not_local_fork);

        // a fork was taken if there are paths that already forked OR this fork triggered
        let fork_guard = pg.or_guard(self.fork_guard, local_fork_guard);
        Self {
            no_fork_guard: simplify_guard(pg, no_fork_guard),
            fork_guard: simplify_guard(pg, fork_guard),
        }
    }

    /// converts information about the guards into a statement about whether a fork might've occurred so far
    fn reachability(self, pg: &mut ProtoGraph) -> ForkReachability {
        let no_fork_guard = simplify_guard(pg, self.no_fork_guard);
        let fork_guard = simplify_guard(pg, self.fork_guard);

        match (check_sat(pg, no_fork_guard), check_sat(pg, fork_guard)) {
            // if both a fork happening and not happening is unsat, this is the bottom which would only happen for totally unreachable nodes?
            (SatResult::DefinitelyUnsat, SatResult::DefinitelyUnsat) => {
                ForkReachability::Unreachable
            }
            // if the fork guard is unsat, then we definitely didn't fork
            (_, SatResult::DefinitelyUnsat) => ForkReachability::DefinitelyNotForked,

            // if the not fork guard is unsat and the fork guard is true, we definitely forked
            (SatResult::DefinitelyUnsat, SatResult::AlwaysSat) => {
                ForkReachability::DefinitelyForked
            }

            _ => ForkReachability::MaybeForked,
        }
    }
}

pub fn reaching_forks_from(pg: &mut ProtoGraph, start: NodeId) -> ForkReach {
    // let reachable = reachable_node_ids(pg, start);
    let preds = predecessors(pg, start);
    let mut in_facts: FxHashMap<NodeId, ForkFact> = FxHashMap::default();
    let mut out: FxHashMap<NodeId, ForkFact> = FxHashMap::default();
    let node_ids: Vec<NodeId> = reachable_node_ids(pg, start);
    let mut worklist = node_ids.clone();

    while let Some(id) = worklist.pop() {
        // initialize the in_fact
        let mut in_fact = if id == start {
            ForkFact::initial(pg)
        } else {
            ForkFact::bottom(pg)
        };

        // compute the in fact by merging across all predecessors, simplifying guards given
        // we know the edges taken
        for (pred_id, transition_guard) in preds.get(&id).into_iter().flatten() {
            let pred_fact = out.get(pred_id).copied().unwrap_or(ForkFact::bottom(pg));

            let edge_no_fork_guard =
                restrict_branch_to_edge(pg, pred_fact.no_fork_guard, *transition_guard)
                    .unwrap_or_else(|| pg.false_id());
            let edge_fork_guard =
                restrict_branch_to_edge(pg, pred_fact.fork_guard, *transition_guard)
                    .unwrap_or_else(|| pg.false_id());
            if edge_no_fork_guard == pg.false_id() && edge_fork_guard == pg.false_id() {
                continue;
            }

            in_fact = ForkFact::merge(
                pg,
                in_fact,
                ForkFact {
                    no_fork_guard: edge_no_fork_guard,
                    fork_guard: edge_fork_guard,
                },
            );
        }

        // compute the current nodes fork guard. `guards` should always be a singleton
        // by the invariants of the compiler, but we can handle multiple by OR-ing them
        let guards = pg[id]
            .actions
            .iter()
            .filter_map(|action| matches!(pg[action.op], Op::Fork).then_some(action.guard))
            .collect_vec();

        let guard = guards.into_iter().fold(pg.false_id(), |guard, fork_guard| {
            pg.or_guard(guard, fork_guard)
        });
        let fork_guard = simplify_guard(pg, guard);

        // compute the transfer, update the facts map, and re-enqueue successors
        // if things have changed
        let new_out = in_fact.transfer(pg, fork_guard);
        if in_facts.get(&id) != Some(&in_fact) || out.get(&id) != Some(&new_out) {
            in_facts.insert(id, in_fact);
            out.insert(id, new_out);
            worklist.extend(pg[id].transitions.iter().map(|t| t.target).unique());
        }
    }

    // convert the facts into our reachability enum
    let mut in_reach = FxHashMap::default();
    let mut out_reach = FxHashMap::default();

    for id in node_ids {
        let in_fact = in_facts.get(&id).copied().unwrap_or(ForkFact::bottom(pg));
        let out_fact = out.get(&id).copied().unwrap_or(ForkFact::bottom(pg));
        in_reach.insert(id, in_fact.reachability(pg));
        out_reach.insert(id, out_fact.reachability(pg));
    }

    ForkReach {
        in_reach,
        out_reach,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::ast::ProtocolContext;
    use crate::frontend::symbol::ROOT_SCOPE;
    use crate::ir::proto_graph::{Action, Node, Transition};

    fn test_graph() -> ProtoGraph {
        ProtoGraph::new(ProtocolContext::new("test".into(), ROOT_SCOPE))
    }

    fn push_fork(pg: &mut ProtoGraph, node_id: NodeId) {
        let fork = pg.o(Op::Fork);
        pg.push_action(node_id, Action::new(pg.true_id(), fork));
    }

    fn push_guarded_fork(pg: &mut ProtoGraph, node_id: NodeId, guard: ExprRef) {
        let fork = pg.o(Op::Fork);
        pg.push_action(node_id, Action::new(guard, fork));
    }

    fn fork_reachability_at(pg: &mut ProtoGraph, id: NodeId) -> ForkReachability {
        reaching_forks_from(pg, pg.entry)
            .out_reach
            .get(&id)
            .copied()
            .unwrap_or(ForkReachability::Unreachable)
    }

    // straight line code with unconditional fork gives "DefinitelyForked"
    #[test]
    fn classifies_definitely_forked_after_fork() {
        let mut pg = test_graph();
        let fork = pg.n(Node::empty());
        let exit = pg.n(Node::empty());

        push_fork(&mut pg, fork);
        let true_id = pg.true_id();
        pg.push_transition(pg.entry, Transition::new(true_id, fork, false));
        pg.push_transition(fork, Transition::new(true_id, exit, false));

        assert_eq!(
            fork_reachability_at(&mut pg, exit),
            ForkReachability::DefinitelyForked
        );
    }

    #[test]
    // straight line code with MaybeSat fork gives "DefinitelyForked"
    fn classifies_guarded_fork_as_maybe_forked() {
        let mut pg = test_graph();
        let fork = pg.n(Node::empty());
        let exit = pg.n(Node::empty());
        let p = pg.expr_ctx.bv_symbol("p", 1);

        push_guarded_fork(&mut pg, fork, p);
        let true_id = pg.true_id();
        pg.push_transition(pg.entry, Transition::new(true_id, fork, false));
        pg.push_transition(fork, Transition::new(true_id, exit, false));

        assert_eq!(
            fork_reachability_at(&mut pg, exit),
            ForkReachability::MaybeForked
        );
    }

    // straight line code without a fork gives "DefinitelyNotForked"
    #[test]
    fn classifies_definitely_not_forked_without_fork() {
        let mut pg = test_graph();
        let exit = pg.n(Node::empty());

        let true_id = pg.true_id();
        pg.push_transition(pg.entry, Transition::new(true_id, exit, false));

        assert_eq!(
            fork_reachability_at(&mut pg, exit),
            ForkReachability::DefinitelyNotForked
        );
    }

    #[test]
    fn classifies_maybe_forked_at_join() {
        let mut pg = test_graph();
        let fork = pg.n(Node::empty());
        let no_fork = pg.n(Node::empty());
        let join = pg.n(Node::empty());

        // entry -> node with fork -> join
        // entry -> node without fork -> join

        push_fork(&mut pg, fork);
        let true_id = pg.true_id();
        pg.push_transition(pg.entry, Transition::new(true_id, fork, false));
        pg.push_transition(pg.entry, Transition::new(true_id, no_fork, false));
        pg.push_transition(fork, Transition::new(true_id, join, false));
        pg.push_transition(no_fork, Transition::new(true_id, join, false));

        assert_eq!(
            fork_reachability_at(&mut pg, join),
            ForkReachability::MaybeForked
        );
    }

    #[test]
    fn transition_guard_refines_guarded_fork() {
        let mut pg = test_graph();
        let fork = pg.n(Node::empty());
        let forked_exit = pg.n(Node::empty());
        let not_forked_exit = pg.n(Node::empty());
        let p = pg.expr_ctx.bv_symbol("p", 1);
        let not_p = pg.not_guard(p);

        // entry -> [p] fork [p]-> forked_exit
        // entry -> [p] fork [!p]-> not-forked_exit

        push_guarded_fork(&mut pg, fork, p);
        let true_id = pg.true_id();
        pg.push_transition(pg.entry, Transition::new(true_id, fork, false));
        pg.push_transition(fork, Transition::new(p, forked_exit, false));
        pg.push_transition(fork, Transition::new(not_p, not_forked_exit, false));

        assert_eq!(
            fork_reachability_at(&mut pg, forked_exit),
            ForkReachability::DefinitelyForked
        );
        assert_eq!(
            fork_reachability_at(&mut pg, not_forked_exit),
            ForkReachability::DefinitelyNotForked
        );
    }
}
