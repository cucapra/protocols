// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use baa::BitVecValue;
use patronus::expr::{ExprRef, Type as PatronusType};
use rustc_hash::FxHashMap;

use crate::Value;
use crate::frontend::ast::{BinOp, Expr, ExprId, Protocol, ProtocolContext, Stmt, StmtId, UnaryOp};
use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::edge_contract::{contract_edges, graft_contracted_entry};
use crate::ir::proto_graph::*;

/// Per-transaction substitution of argument symbols to concrete expressions.
///
/// In the trace-aware lowering, every argument is replaced by a constant
/// (`bv_lit`) drawn from the trace, so the same argument `SymbolId` can map to
/// different values in different transaction copies. This is kept separate from
/// the graph-wide `symbol_expr` cache (which is shared across copies and holds
/// only ports and other genuinely shared symbols).
type ArgSubst = FxHashMap<SymbolId, ExprRef>;

/// The result of lowering one protocol body into a (possibly shared) graph.
struct LoweredProtocol {
    /// First node allocated for this copy.
    first_node: NodeId,
    /// Entry node of the lowered body.
    entry: NodeId,
    /// The body's exit node (carries `Done` only for the final transaction).
    done: NodeId,
    /// Every node in this ProtoGraph that performs an explicit `Fork`.
    forks: Vec<NodeId>,
}

/// TODO: we can get rid of this function
/// TODO: maybe done should always be grafted?
fn next_frontier(lowered: &LoweredProtocol) -> (Vec<NodeId>, bool) {
    if lowered.forks.is_empty() {
        (vec![lowered.done], false)
    } else {
        (lowered.forks.clone(), false)
    }
}

fn contracted_next_frontier(ir: &ProtoGraph, lowered: &LoweredProtocol) -> Vec<(NodeId, ExprRef)> {
    let forks: Vec<(NodeId, ExprRef)> = ir
        .nodes()
        // TODO: ir >= lowered.first_node is kinda a janky way to check that we're in the latest trace
        .filter(|(id, _)| *id >= lowered.first_node)
        .flat_map(|(id, node)| {
            node.actions
                .iter()
                .filter(|action| matches!(ir[action.op], Op::Fork))
                .map(move |action| (id, action.guard))
        })
        .collect();

    if forks.is_empty() {
        vec![(lowered.done, ir.true_id())]
    } else {
        forks
    }
}

/// Stateful driver that lowers AST protocols into a `ProtoGraph`.
///
/// It owns the graph being built, borrows the `SymbolTable`, and carries the
/// current argument substitution so the recursive lowering routines don't have
/// to thread those through every call. `subst` is empty for the classic
/// trace-agnostic path and is replaced per transaction in the trace-aware path.
struct Lowerer<'a> {
    ir: ProtoGraph,
    symbols: &'a SymbolTable,
    subst: ArgSubst,
}

impl<'a> Lowerer<'a> {
    fn new(ctx: ProtocolContext, symbols: &'a SymbolTable) -> Self {
        Self {
            ir: ProtoGraph::new(ctx),
            symbols,
            subst: ArgSubst::default(),
        }
    }

    fn lower_expr(
        &mut self,
        ast: &Protocol,
        expr: ExprId,
        expected: Option<PatronusType>,
    ) -> ExprRef {
        match &ast[expr] {
            Expr::DontCare => {
                let tpe = expected.unwrap_or(PatronusType::BV(1));
                let next_dont_care = self.ir.dont_cares.len();
                // the name here is not relevant for anything other than debugging
                let name = format!("dont_care_{}", next_dont_care);
                let dont_care_expr = match tpe {
                    PatronusType::BV(width) => self.ir.expr_ctx.bv_symbol(&name, width),
                    PatronusType::Array(array_tpe) => self.ir.expr_ctx.array_symbol(
                        &name,
                        array_tpe.index_width,
                        array_tpe.data_width,
                    ),
                };
                self.ir.dont_cares.insert(dont_care_expr);
                dont_care_expr
            }
            Expr::Const(bvv) => self.ir.expr_ctx.bv_lit(bvv),
            Expr::Sym(sym) => self.lower_symbol(*sym),
            Expr::Binary(BinOp::Equal, lhs, rhs) => {
                let lhs_ref = self.lower_expr(ast, *lhs, None);
                let rhs_ref = self.lower_expr(ast, *rhs, None);
                self.ir.expr_ctx.equal(lhs_ref, rhs_ref)
            }
            Expr::Binary(BinOp::Concat, lhs, rhs) => {
                let lhs_ref = self.lower_expr(ast, *lhs, None);
                let rhs_ref = self.lower_expr(ast, *rhs, None);
                self.ir.expr_ctx.concat(lhs_ref, rhs_ref)
            }
            Expr::Binary(BinOp::Add, lhs, rhs) => {
                let lhs_ref = self.lower_expr(ast, *lhs, None);
                let rhs_ref = self.lower_expr(ast, *rhs, None);
                self.ir.expr_ctx.add(lhs_ref, rhs_ref)
            }
            Expr::Binary(BinOp::And, lhs, rhs) => {
                let lhs_ref = self.lower_expr(ast, *lhs, None);
                let rhs_ref = self.lower_expr(ast, *rhs, None);
                self.ir.expr_ctx.and(lhs_ref, rhs_ref)
            }
            Expr::Unary(UnaryOp::Not, inner) => {
                let inner_ref = self.lower_expr(ast, *inner, Some(PatronusType::BV(1)));
                self.ir.expr_ctx.not(inner_ref)
            }
            Expr::Slice(inner, hi, lo) => {
                let (hi, lo) = (*hi, *lo);
                let inner_ref = self.lower_expr(ast, *inner, None);
                self.ir.expr_ctx.slice(inner_ref, hi, lo)
            }
            Expr::IsLastIteration => {
                panic!("loop expressions are not lowered to Patronus yet")
            }
            Expr::IterCount(_) => {
                panic!("loop expressions are not lowered to Patronus yet")
            }
        }
    }

    fn lower_symbol(&mut self, symbol_id: SymbolId) -> ExprRef {
        // A trace-substituted argument takes precedence over the shared cache:
        // the same argument symbol may resolve to different constants per copy.
        if let Some(expr) = self.subst.get(&symbol_id) {
            return *expr;
        }

        if let Some(expr) = self.ir.symbol_expr(symbol_id) {
            return expr;
        }

        let symbols = self.symbols;
        let entry = &symbols[symbol_id];
        let full_name = entry.full_name(symbols);
        let expr = match entry.tpe() {
            FrontType::BitVec(width) => self.ir.expr_ctx.bv_symbol(&full_name, width),
            FrontType::Struct(_)
            | FrontType::Seq(_)
            | FrontType::UnsignedInt
            | FrontType::Unknown => {
                panic!(
                    "unsupported symbol type {} for {}",
                    crate::frontend::serialize::serialize_type(symbols, entry.tpe()),
                    full_name
                )
            }
        };
        self.ir.cache_symbol_expr(symbol_id, expr);
        expr
    }

    // lower some statement `stmt_id` (which points to a subtree in the AST) to
    // an IR where the final node in the IR sub-graph points to an exit node `exit`
    fn lower_stmt(&mut self, ast: &Protocol, stmt_id: StmtId, exit: NodeId) -> NodeId {
        match &ast[stmt_id] {
            Stmt::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    let node_id = self.ir.n(Node::empty());
                    let true_id = self.ir.true_id();
                    self.ir
                        .push_transition(node_id, Transition::new(true_id, exit, false));
                    return node_id;
                }

                let mut curr_exit = exit;
                for stmt_id in stmt_ids.clone().iter().rev() {
                    curr_exit = self.lower_stmt(ast, *stmt_id, curr_exit);
                }
                curr_exit
            }
            Stmt::Assign(symbol_id, expr_id) => {
                let (symbol_id, expr_id) = (*symbol_id, *expr_id);
                let node_id = self.ir.n(Node::empty());
                let default_value = self.lower_symbol(symbol_id);
                let expected = match self.symbols[symbol_id].tpe() {
                    FrontType::BitVec(width) => PatronusType::BV(width),
                    other => panic!(
                        "unsupported assignment target type for Patronus lowering: {:?}",
                        other
                    ),
                };
                let rhs_ref = self.lower_expr(ast, expr_id, Some(expected));
                let guard = self.ir.true_id();
                let rhs_ref = self.ir.expr_ctx.ite(guard, rhs_ref, default_value);
                let op_id = self.ir.o(Op::Assign(symbol_id, rhs_ref));
                let true_id = self.ir.true_id();
                self.ir.push_action(node_id, Action::new(true_id, op_id));
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, false));
                node_id
            }
            Stmt::Step => {
                let node_id = self.ir.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, true));
                node_id
            }
            Stmt::Fork => {
                let node_id = self.ir.n(Node::empty());
                let op_id = self.ir.o(Op::Fork);
                let true_id = self.ir.true_id();
                self.ir.push_action(node_id, Action::new(true_id, op_id));
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, false));
                node_id
            }
            Stmt::AssertEq(lhs, rhs) => {
                let (lhs, rhs) = (*lhs, *rhs);
                let node_id = self.ir.n(Node::empty());
                let lhs_ref = self.lower_expr(ast, lhs, None);
                let rhs_ref = self.lower_expr(ast, rhs, None);
                let op_id = self.ir.o(Op::AssertEq(lhs_ref, rhs_ref));
                let true_id = self.ir.true_id();
                self.ir.push_action(node_id, Action::new(true_id, op_id));
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, false));
                node_id
            }
            Stmt::IfElse(cond, true_branch, false_branch) => {
                let (cond, true_branch, false_branch) = (*cond, *true_branch, *false_branch);
                // create a join node that will be the final node in the IfElse subgraph, pointing to exit
                // this will also be the target exit node for the sub-branches
                let join_node_id = self.ir.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(join_node_id, Transition::new(true_id, exit, false));

                let true_entry = self.lower_stmt(ast, true_branch, join_node_id);
                let false_entry = self.lower_stmt(ast, false_branch, join_node_id);

                // create the branch node from which we transition into the true or false entry nodes
                let branch_node_id = self.ir.n(Node::empty());
                let cond_ref = self.lower_expr(ast, cond, Some(PatronusType::BV(1)));
                let negated_cond = self.ir.expr_ctx.not(cond_ref);

                // push transitions from the branch node to the true/false branch with positive/negative guarded transitions
                self.ir
                    .push_transition(branch_node_id, Transition::new(cond_ref, true_entry, false));
                self.ir.push_transition(
                    branch_node_id,
                    Transition::new(negated_cond, false_entry, false),
                );
                branch_node_id
            }
            // FIXME: not sure if there is a better word than "guard" here. worried about overloading that term.
            // maybe just "cond"?
            Stmt::While(loop_guard, loop_body) => {
                let (loop_guard, loop_body) = (*loop_guard, *loop_body);
                let loop_exit_node_id = self.ir.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(loop_exit_node_id, Transition::new(true_id, exit, false));

                // create the loop guard.node from which we transition into the loop body or loop exit nodes
                let loop_guard_node_id = self.ir.n(Node::empty());

                // lower the loop body, which exits into the loop guard (the cycle-forming edge)
                let loop_body_node_id = self.lower_stmt(ast, loop_body, loop_guard_node_id);

                // create transitions from the loop guard to the loop body and the loop exit
                let loop_guard_ref = self.lower_expr(ast, loop_guard, Some(PatronusType::BV(1)));
                let negated_loop_guard = self.ir.expr_ctx.not(loop_guard_ref);
                self.ir.push_transition(
                    loop_guard_node_id,
                    Transition::new(loop_guard_ref, loop_body_node_id, false),
                );
                self.ir.push_transition(
                    loop_guard_node_id,
                    Transition::new(negated_loop_guard, loop_exit_node_id, false),
                );

                loop_guard_node_id
            }
            Stmt::RepeatLoop(_expr_id, _stmt_id) => todo!(),
            Stmt::ForInLoop(_symbol_id, _expr_id, _stmt_id) => todo!(),
        }
    }

    /// Lower `ast`'s body into the graph using the current `subst`. Appends a
    /// fresh `Done` node plus the body's nodes; reports the body entry and the
    /// fork nodes belonging to this copy. Shared symbols (ports) are interned in
    /// the `symbol_expr` cache and therefore unified across copies.
    fn lower_protocol_body(&mut self, ast: &Protocol, keep_done: bool) -> LoweredProtocol {
        // mark the start of this copy's node range so we can find its fork nodes
        let first_new = self.ir.next_node_id();

        let done = self.ir.n(Node::empty());
        if keep_done {
            let done_op = self.ir.o(Op::Done);
            let true_id = self.ir.true_id();
            self.ir.push_action(done, Action::new(true_id, done_op));
        }

        let entry = self.lower_stmt(ast, ast.body, done);

        let forks: Vec<NodeId> = self
            .ir
            .nodes()
            .filter(|(id, _)| *id >= first_new)
            .filter(|(_, node)| {
                node.actions
                    .iter()
                    .any(|a| matches!(self.ir[a.op], Op::Fork))
            })
            .map(|(id, _)| id)
            .collect();

        LoweredProtocol {
            first_node: first_new,
            entry,
            done,
            forks,
        }
    }

    /// Build the per-copy argument substitution (argument symbol -> constant)
    /// and lower one transaction's body into the graph.
    fn lower_transaction(
        &mut self,
        ast: &Protocol,
        values: &[Value],
        keep_done: bool,
    ) -> LoweredProtocol {
        assert_eq!(
            ast.args.len(),
            values.len(),
            "argument count mismatch for protocol {}",
            ast.name
        );
        let mut subst = ArgSubst::default();
        for (arg, value) in ast.args.iter().zip(values) {
            let bvv: BitVecValue = value
                .clone()
                .try_into()
                .unwrap_or_else(|_| panic!("unsupported argument type for {}", ast.name));
            let lit = self.ir.expr_ctx.bv_lit(&bvv);
            subst.insert(arg.symbol(), lit);
        }
        self.subst = subst;
        self.lower_protocol_body(ast, keep_done)
    }

    /// For the next trace element, hang a fresh copy of its protocol off each
    /// node in `frontier`, then recurse on that copy's own frontier. `frontier`
    /// and `consumes_step` come from [`next_frontier`] applied to the previous
    /// copy: explicit forks graft via epsilon edges, an implicit fork (the exit
    /// node) grafts via a step edge. Each frontier node gets its own copy (and
    /// downstream chain); with at most one fork per protocol this is a linear
    /// chain with no blowup.
    fn graft_frontier(
        &mut self,
        frontier: Vec<NodeId>,
        consumes_step: bool,
        remaining: &[(String, Vec<Value>)],
        protos_by_name: &FxHashMap<&str, &Protocol>,
    ) {
        let Some(((name, values), rest)) = remaining.split_first() else {
            return;
        };

        // there are transactions left to graft, so we must have somewhere to
        // graft them onto
        if frontier.is_empty() {
            panic!(
                "{} transaction(s) remain in the trace but the previous transaction \
                 exposed no fork points to graft onto",
                remaining.len()
            );
        }

        let ast = *protos_by_name
            .get(name.as_str())
            .unwrap_or_else(|| panic!("unknown protocol {name}"));

        // this transaction is the last in its chain iff nothing follows it
        let keep_done = rest.is_empty();

        for node in frontier {
            let copy = self.lower_transaction(ast, values, keep_done);
            // graft the next transaction's entry onto this frontier node. A
            // real fork uses an epsilon edge (concurrent start); an implicit
            // fork at the exit node uses a step edge (sequential start).
            let true_id = self.ir.true_id();
            self.ir
                .push_transition(node, Transition::new(true_id, copy.entry, consumes_step));
            let (next, next_step) = next_frontier(&copy);
            self.graft_frontier(next, next_step, rest, protos_by_name);
        }
    }

    /// Like [`Self::graft_frontier`], but each transaction copy is contracted
    /// before it is attached, and the copy entry is merged directly into each
    /// frontier node. That preserves edge-contraction assignment ordering at
    /// the graft point without introducing another epsilon edge.
    fn graft_contracted_frontier(
        &mut self,
        frontier: Vec<(NodeId, ExprRef)>,
        remaining: &[(String, Vec<Value>)],
        protos_by_name: &FxHashMap<&str, &Protocol>,
    ) {
        let Some(((name, values), rest)) = remaining.split_first() else {
            return;
        };

        if frontier.is_empty() {
            panic!(
                "{} transaction(s) remain in the trace but the previous transaction \
                 exposed no fork points to graft onto",
                remaining.len()
            );
        }

        let ast = *protos_by_name
            .get(name.as_str())
            .unwrap_or_else(|| panic!("unknown protocol {name}"));
        let keep_done = rest.is_empty();

        let copy = self.lower_transaction(ast, values, keep_done);
        contract_edges(&mut self.ir, self.symbols);
        let next = contracted_next_frontier(&self.ir, &copy);

        for (node, guard) in frontier {
            graft_contracted_entry(&mut self.ir, self.symbols, node, copy.entry, guard);
        }

        self.graft_contracted_frontier(next, rest, protos_by_name);
    }
}

/// Lower a single AST `Protocol` into a fresh `ProtoGraph` (the classic,
/// trace-agnostic path). Arguments remain symbolic.
pub fn lower_ast_to_ir(ast: Protocol, symbols: &SymbolTable) -> ProtoGraph {
    let mut lowerer = Lowerer::new(ast.ctx.clone(), symbols);
    let lowered = lowerer.lower_protocol_body(&ast, true);
    let entry_node = lowerer.ir.entry;
    let true_id = lowerer.ir.true_id();
    lowerer
        .ir
        .push_transition(entry_node, Transition::new(true_id, lowered.entry, false));
    lowerer.ir
}

/// Lower a whole trace of known transactions into a single joint `ProtoGraph`.
///
/// The first transaction becomes the graph entry; each subsequent transaction
/// is grafted onto the fork nodes of the previous one. Arguments are
/// substituted with the concrete values from the trace, while ports are shared
/// across all copies. The caller is expected to run `contract_edges` /
/// `normalize_assignments` on the result.
pub fn lower_trace_to_ir(
    trace: &[(String, Vec<Value>)],
    protos_by_name: &FxHashMap<&str, &Protocol>,
    symbols: &SymbolTable,
) -> ProtoGraph {
    assert!(!trace.is_empty(), "cannot lower an empty trace");

    let (first_name, first_values) = &trace[0];
    let first_ast = *protos_by_name
        .get(first_name.as_str())
        .unwrap_or_else(|| panic!("unknown protocol {first_name}"));

    let mut lowerer = Lowerer::new(first_ast.ctx.clone(), symbols);
    // the first transaction is the last one only when the trace has length 1
    let first = lowerer.lower_transaction(first_ast, first_values, trace.len() == 1);
    let entry_node = lowerer.ir.entry;
    let true_id = lowerer.ir.true_id();
    lowerer
        .ir
        .push_transition(entry_node, Transition::new(true_id, first.entry, false));
    let (frontier, consumes_step) = next_frontier(&first);
    lowerer.graft_frontier(frontier, consumes_step, &trace[1..], protos_by_name);
    lowerer.ir
}

/// Lower a whole trace to one graph while contracting each transaction copy
/// before grafting it into the prior copy's frontier.
///
/// The final graph has no epsilon graft edges; after all grafting, callers may
/// run one determinization pass over the already-contracted joint graph.
pub fn lower_trace_to_contracted_ir(
    trace: &[(String, Vec<Value>)],
    protos_by_name: &FxHashMap<&str, &Protocol>,
    symbols: &SymbolTable,
) -> ProtoGraph {
    assert!(!trace.is_empty(), "cannot lower an empty trace");

    let (first_name, first_values) = &trace[0];
    let first_ast = *protos_by_name
        .get(first_name.as_str())
        .unwrap_or_else(|| panic!("unknown protocol {first_name}"));

    let mut lowerer = Lowerer::new(first_ast.ctx.clone(), symbols);
    let first = lowerer.lower_transaction(first_ast, first_values, trace.len() == 1);
    let entry_node = lowerer.ir.entry;
    let true_id = lowerer.ir.true_id();
    lowerer
        .ir
        .push_transition(entry_node, Transition::new(true_id, first.entry, false));
    contract_edges(&mut lowerer.ir, symbols);

    let frontier = contracted_next_frontier(&lowerer.ir, &first);
    lowerer.graft_contracted_frontier(frontier, &trace[1..], protos_by_name);
    lowerer.ir
}
