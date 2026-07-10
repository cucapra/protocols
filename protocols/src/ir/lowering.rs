// Copyright 2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>

use patronus::expr::{Context as ExprContext, ExprRef, Type as PatronusType};
use rustc_hash::FxHashMap;

use crate::frontend::ast::{BinOp, Expr, ExprId, Protocol, ProtocolContext, Stmt, StmtId, UnaryOp};
use crate::frontend::symbol::{SymbolId, SymbolTable, Type as FrontType};
use crate::ir::edge_contract::contract_edges;
use crate::ir::fork_reach::{ForkReachability, reaching_forks_from};
use crate::ir::propagate_assigns::propagate_assignments_from;
use crate::ir::proto_graph::*;
use crate::ir::reaching_defs::reaching_definitions;

/// substitution of argument symbols to concrete expressions for trace lowering
pub type TraceArgSubst = FxHashMap<SymbolId, ExprRef>;

/// Information about the result of lowering an AST to a graph fragment.
pub struct LoweredFragmentInfo {
    /// Nodes allocated for this fragment.
    pub nodes: Vec<NodeId>,
    /// Entry node of the fragment.
    pub entry: NodeId,
    /// Exit node of the fragment.
    pub exit: NodeId,
}

/// The stateful driver of lowering an AST to an IR
pub struct Lowerer<'a> {
    pub ir: ProtoGraph,
    pub symbols: &'a SymbolTable,
    /// Optional substitution of args for concrete values
    pub trace_arg_subst: TraceArgSubst,
    /// The nodes from the most recent lowered fragment.
    current_fragment_nodes: Vec<NodeId>,
}

impl<'a> Lowerer<'a> {
    pub fn new(ctx: ProtocolContext, symbols: &'a SymbolTable) -> Self {
        Self {
            ir: ProtoGraph::new(ctx),
            symbols,
            trace_arg_subst: TraceArgSubst::default(),
            current_fragment_nodes: Vec::new(),
        }
    }

    pub fn with_expr_ctx(
        ctx: ProtocolContext,
        symbols: &'a SymbolTable,
        expr_ctx: ExprContext,
    ) -> Self {
        Self {
            ir: ProtoGraph::with_expr_ctx(ctx, expr_ctx),
            symbols,
            trace_arg_subst: TraceArgSubst::default(),
            current_fragment_nodes: Vec::new(),
        }
    }

    pub fn postprocess_trace_fragment(&mut self, fragment: &LoweredFragmentInfo) {
        // The newly lowered transaction is still disconnected from the existing
        // trace graph, so propagation has to start from the fragment entry.
        contract_edges(&mut self.ir, self.symbols);
        let rd = reaching_definitions(&mut self.ir, self.symbols);
        propagate_assignments_from(&mut self.ir, self.symbols, &rd, fragment.entry);
    }

    pub fn graft_points(&mut self, fragment: &LoweredFragmentInfo) -> Vec<(NodeId, ExprRef)> {
        let fork_reach = reaching_forks_from(&mut self.ir, fragment.entry);
        let ir = &self.ir;

        // find all the forks in the IR that are within this lowered fragment (the most recent transaction we lowered).
        // TODO: instead of reachability, we should just run garbage collection
        let mut graft_points: Vec<(NodeId, ExprRef)> = fragment
            .nodes
            .iter()
            .flat_map(|id| {
                let reachability = fork_reach
                    .in_reach
                    .get(id)
                    .copied()
                    .unwrap_or(ForkReachability::Unreachable);

                if reachability != ForkReachability::DefinitelyNotForked {
                    return Vec::new().into_iter();
                }

                let node = &ir[*id];
                node.actions
                    .iter()
                    .filter(|action| matches!(ir[action.op], Op::Fork))
                    .map(move |action| (*id, action.guard))
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .collect();

        // at every fork point, we want to have it proven that we haven't forked before
        for (fork_node, _) in &graft_points {
            let reachability = fork_reach.in_reach.get(fork_node).copied().unwrap();
            assert!(
                matches!(
                    reachability,
                    // nodes never get cleaned up, so there are old (pre-contraction) fork nodes that are Unreachable we need to account for
                    ForkReachability::Unreachable | ForkReachability::DefinitelyNotForked
                ),
                "fork node {fork_node} can be reached after a prior fork"
            );
        }

        // if we can prove we haven't forked up to know, we'll also graft onto the exit
        // if we can prove we have forked up to know, we won't graft onto the exit node
        // otherwise, panic! - we're gonna have an exponential blowup
        let exit_reachability = fork_reach
            .in_reach
            .get(&fragment.exit)
            .copied()
            .unwrap_or(ForkReachability::Unreachable);
        match exit_reachability {
            ForkReachability::DefinitelyNotForked => {
                graft_points.push((fragment.exit, self.ir.true_id()));
            }
            ForkReachability::DefinitelyForked | ForkReachability::Unreachable => {}
            ForkReachability::MaybeForked => {
                panic!("done node {} may or may not have forked", fragment.exit);
            }
        }

        graft_points
    }

    /// Add a new node to the IR and track it in current fragment
    fn n(&mut self, node: Node) -> NodeId {
        let node_id = self.ir.n(node);
        self.current_fragment_nodes.push(node_id);
        node_id
    }

    fn dont_care_expr(&mut self, tpe: PatronusType) -> ExprRef {
        let next_dont_care = self.ir.dont_cares.len();
        let name = format!("dont_care_{}", next_dont_care);
        let dont_care_expr = match tpe {
            PatronusType::BV(width) => self.ir.expr_ctx.bv_symbol(&name, width),
            PatronusType::Array(array_tpe) => {
                self.ir
                    .expr_ctx
                    .array_symbol(&name, array_tpe.index_width, array_tpe.data_width)
            }
        };
        self.ir.dont_cares.insert(dont_care_expr);
        dont_care_expr
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
                self.dont_care_expr(tpe)
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
        if let Some(expr) = self.trace_arg_subst.get(&symbol_id) {
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
                    let node_id = self.n(Node::empty());
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
                let node_id = self.n(Node::empty());
                let expected = match self.symbols[symbol_id].tpe() {
                    FrontType::BitVec(width) => PatronusType::BV(width),
                    other => panic!(
                        "unsupported assignment target type for Patronus lowering: {:?}",
                        other
                    ),
                };
                let rhs_ref = self.lower_expr(ast, expr_id, Some(expected));
                let assignment = Assignment::from_rhs(
                    self.ir.false_id(),
                    self.ir.true_id(),
                    rhs_ref,
                    self.ir.dont_cares.contains(&rhs_ref),
                );
                let op_id = self.ir.o(Op::Assign(symbol_id, assignment));
                let true_id = self.ir.true_id();
                self.ir.push_action(node_id, Action::new(true_id, op_id));
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, false));
                node_id
            }
            Stmt::Step => {
                let node_id = self.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, true));
                node_id
            }
            Stmt::Fork => {
                let node_id = self.n(Node::empty());
                let op_id = self.ir.o(Op::Fork);
                let true_id = self.ir.true_id();
                self.ir.push_action(node_id, Action::new(true_id, op_id));
                self.ir
                    .push_transition(node_id, Transition::new(true_id, exit, false));
                node_id
            }
            Stmt::AssertEq(lhs, rhs) => {
                let (lhs, rhs) = (*lhs, *rhs);
                let node_id = self.n(Node::empty());
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
                let join_node_id = self.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(join_node_id, Transition::new(true_id, exit, false));

                let true_entry = self.lower_stmt(ast, true_branch, join_node_id);
                let false_entry = self.lower_stmt(ast, false_branch, join_node_id);

                // create the branch node from which we transition into the true or false entry nodes
                let branch_node_id = self.n(Node::empty());
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
                let loop_exit_node_id = self.n(Node::empty());
                let true_id = self.ir.true_id();
                self.ir
                    .push_transition(loop_exit_node_id, Transition::new(true_id, exit, false));

                // create the loop guard.node from which we transition into the loop body or loop exit nodes
                let loop_guard_node_id = self.n(Node::empty());

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

    fn add_input_dont_care_assignments(&mut self, ast: &Protocol, node_id: NodeId) {
        let dut = ast.ctx.dut_sym;

        for input in self
            .symbols
            .get_children(&dut)
            .filter(|sym| self.symbols[*sym].is_in_port())
        {
            let assignment = Assignment::dont_care(self.ir.true_id());
            let assign = self.ir.o(Op::Assign(input, assignment));
            self.ir
                .push_action(node_id, Action::new(self.ir.true_id(), assign));
        }
    }

    /// lowers an AST into fresh IR nodes which are unconnected to any existing IR nodes
    /// If `keep_done`, then the exit node has the Done action.
    /// Returns the nodes, entry, and exit of the lowered fragment
    pub fn lower_protocol_fragment(
        &mut self,
        ast: &Protocol,
        keep_done: bool,
    ) -> LoweredFragmentInfo {
        debug_assert!(
            self.current_fragment_nodes.is_empty(),
            "fragment node accumulator should be empty before
          lowering a fragment"
        );

        let done = self.n(Node::empty());
        if keep_done {
            let done_op = self.ir.o(Op::Done);
            let true_id = self.ir.true_id();
            self.ir.push_action(done, Action::new(true_id, done_op));
        }

        // relinquish all ports in the exit node
        self.add_input_dont_care_assignments(ast, done);

        // lower the protocol, which will add the new nodes to self.current_fragment_nodes
        let body_entry = self.lower_stmt(ast, ast.body, done);
        let entry = self.n(Node::empty());
        self.add_input_dont_care_assignments(ast, entry);
        let true_id = self.ir.true_id();
        self.ir
            .push_transition(entry, Transition::new(true_id, body_entry, false));
        let nodes = std::mem::take(&mut self.current_fragment_nodes);
        LoweredFragmentInfo {
            nodes,
            entry,
            exit: done,
        }
    }
}

/// Lower a single AST `Protocol` into a fresh symbolic `ProtoGraph`
pub fn lower_ast_to_ir(ast: Protocol, symbols: &SymbolTable) -> ProtoGraph {
    // create a lowerer and lower the ast
    let mut lowerer = Lowerer::new(ast.ctx.clone(), symbols);
    let fragment = lowerer.lower_protocol_fragment(&ast, true);

    // link up the default entry node of the ir with the entry node of the lowered AST
    let entry_node = lowerer.ir.entry;
    let true_id = lowerer.ir.true_id();
    lowerer
        .ir
        .push_transition(entry_node, Transition::new(true_id, fragment.entry, false));

    lowerer.ir.simplify_all_exprs();
    lowerer.ir
}
