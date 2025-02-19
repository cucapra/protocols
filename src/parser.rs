// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecValue;
use pest::iterators::Pairs;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use pest_derive::Parser;
use std::{fmt, io::stdout, process::id, vec};

use crate::serialize::*;
use crate::{diagnostic::*, ir::*};

#[derive(Parser)]
#[grammar = "protocols.pest"]
struct ProtocolParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        // Precedence is defined lowest to highest
        PrattParser::new()
            .op(Op::infix(eq, Left))
            .op(Op::infix(log_and, Left))
            .op(Op::prefix(not))
    };
}

pub struct ParserContext<'a> {
    pub st: &'a mut SymbolTable,
    pub fileid: usize,
    pub tr: &'a mut Transaction,
    pub handler: &'a mut DiagnosticHandler,
}

impl<'a> ParserContext<'a> {
    pub fn parse_boxed_expr(&mut self, pairs: Pairs<Rule>) -> BoxedExpr {
        PRATT_PARSER
            .map_primary(|primary| {
                let start = primary.as_span().start();
                let end = primary.as_span().end();

                match primary.as_rule() {
                    // parse integer literals
                    Rule::integer => {
                        let int_str = primary.as_str();
                        let int_value = int_str.parse::<i32>().unwrap();

                        let bitvec = BitVecValue::from_u64(int_value as u64, 64);
                        BoxedExpr::Const(bitvec, start, end)
                    }

                    // parse path identifiers
                    Rule::path_id => {
                        let path_id = primary.as_str();

                        let symbol_id = self.st.symbol_id_from_name(path_id);
                        match symbol_id {
                            Some(id) => BoxedExpr::Sym(id, start, end),
                            None => {
                                // FIXME: better message
                                self.handler.emit_diagnostic_parsing(&format!("Referencing undefined symbol: {}", path_id), self.fileid, primary, Level::Error);
                                panic!();
                                // std::process::exit(1);
                            },
                        }
                    }

                    // parse don't care
                    Rule::dont_care => BoxedExpr::DontCare(start, end),

                    // parse slices
                    Rule::slice => {
                        let mut inner_rules = primary.into_inner();

                        let path_rule = inner_rules.next().unwrap();
                        let path_id = self.parse_boxed_expr(Pairs::single(path_rule));

                        let idx1_rule: pest::iterators::Pair<'_, Rule> = inner_rules.next().unwrap();
                        let idx1 = idx1_rule.as_str().parse::<u32>().unwrap();

                        let idx2_rule = inner_rules.next();
                        let idx2 = match idx2_rule {
                            Some(rule) => rule.as_str().parse::<u32>().unwrap(),
                            // a[i] is syntactic sugar for a[i:i]
                            None => idx1,
                        };

                        BoxedExpr::Slice(Box::new(path_id), idx1, idx2, start, end)
                    }

                    // if primary is an expression (due to parens), recursively parse its inner constituents
                    Rule::expr => self.parse_boxed_expr(primary.into_inner()),
                    rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
                }
            })
            // Parse binary expressions
            .map_infix(|lhs, op, rhs| {
                // the start and end of the expression is the start of the LHS and the end of the RHS
                let start = lhs.start();
                let end = rhs.end();

                let op = match op.as_rule() {
                    Rule::eq => BinOp::Equal,
                    Rule::log_and => BinOp::And,
                    rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
                };
                BoxedExpr::Binary(op, Box::new(lhs), Box::new(rhs), start, end)
            })
            // Parse unary expressions
            .map_prefix(|op, arg| {
                // the position of the expression is the start of the prefix operator and the end of the argument
                let start = op.as_span().start();
                let end = arg.end();

                let op = match op.as_rule() {
                    Rule::not => UnaryOp::Not,
                    rule => unreachable!("Expr::parse expected prefix operation, found {:?}", rule),
                };
                BoxedExpr::Unary(op, Box::new(arg), start, end)
            })
            .parse(pairs)
    }

    fn boxed_expr_to_expr_id(&mut self, expr: BoxedExpr) -> ExprId {
        match expr {
            BoxedExpr::Const(value, start, end) => {
                let expr_id = self.tr.e(Expr::Const(value));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Sym(symbol_id, start, end) => {
                let expr_id = self.tr.e(Expr::Sym(symbol_id));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::DontCare(start, end) => {
                let expr_id = self.tr.e(Expr::DontCare);
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Binary(op, lhs, rhs, start, end) => {
                let lhs_id = self.boxed_expr_to_expr_id(*lhs);
                let rhs_id = self.boxed_expr_to_expr_id(*rhs);
                let expr_id = self.tr.e(Expr::Binary(op, lhs_id, rhs_id));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Unary(op, arg, start, end) => {
                let arg_id = self.boxed_expr_to_expr_id(*arg);
                let expr_id = self.tr.e(Expr::Unary(op, arg_id));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Slice(expr, idx1, idx2, start, end) => {
                let sym_id = self.boxed_expr_to_expr_id(*expr);
                let expr_id = self.tr.e(Expr::Slice(sym_id, idx1, idx2));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
        }
    }

    fn parse_struct(&mut self, pair: pest::iterators::Pair<Rule>) -> StructId {
        let mut inner_rules = pair.into_inner();
        let struct_name = inner_rules.next().unwrap().as_str();

        let (pins, _symbols) = self.parse_fields(inner_rules.next().unwrap());
        let struct_id = self.st.add_struct(struct_name.to_string(), pins);

        struct_id
    }

    // TODO: Add line numbers and character loc.
    fn parse_transaction(&mut self, pair: pest::iterators::Pair<Rule>) {
        match pair.as_rule() {
            Rule::fun => {
                let mut inner_rules = pair.into_inner();
                let id_pair = inner_rules.next().unwrap();
                let id = id_pair.as_str();
                self.tr.name = id.to_string();

                // Parse the DUT definition
                if let Some(inner_pair) = inner_rules.next() {
                    match inner_pair.as_rule() {
                        Rule::type_param => {
                            let mut type_param_rules = inner_pair.into_inner();
                            let path_id_1 = type_param_rules.next().unwrap().as_str();
                            let path_id_2 = type_param_rules.next().unwrap().as_str();

                            let struct_id = {
                                let struct_id = self.st
                                    .struct_id_from_name(path_id_2)
                                    .expect(&format!("Undefined struct: {}", path_id_2));
                                struct_id
                            };

                            let dut_struct = {
                                let struct_ref = self.st.struct_from_struct_id(struct_id);
                                struct_ref.clone() // Clone if necessary to avoid borrowing issues
                            };

                            let dut_symbol_id =
                                self.st.add_without_parent(path_id_1.to_string(), Type::Struct(struct_id));

                            for pin in dut_struct.pins() {
                                let pin_name = pin.name().to_string();
                                self.st.add_with_parent(pin_name, dut_symbol_id);
                            }
                        }
                        _ => {
                            self.handler.emit_diagnostic_parsing(
                                &format!("Attempted to parse DUT type param. Unexpected rule: {:?}", inner_pair.as_rule()),
                                self.fileid,
                                inner_pair,
                                Level::Error,
                            );
                            panic!();
                        },
                    }
                }

                if let Some(arglist_pair) = inner_rules.peek() {
                    if arglist_pair.as_rule() == Rule::arglist {
                        self.tr.args = self.parse_arglist(inner_rules.next().unwrap());
                    } else {
                        self.tr.args = Vec::new();
                    }
                } else {
                    self.tr.args = Vec::new();
                }

                // Process the body of statements, adding them to the block as we go
                self.tr.body = self.parse_stmt_block(inner_rules);
            }
            _ => {
                self.handler.emit_diagnostic_parsing(
                    &format!("Unexpected rule while parsing transaction: {:?}", pair.as_rule()),
                    self.fileid,
                    pair,
                    Level::Error,
                );
                panic!();
            },
        };
    }

    fn parse_expr(&mut self, pairs: Pairs<Rule>) -> ExprId {
        let boxed_expr = self.parse_boxed_expr(pairs);
        let expr_id = self.boxed_expr_to_expr_id(boxed_expr);

        // print out expr loc for testing
        // println!("Expr: {:?}, Expr loc: {:?}", serialize_expr(tr, st, &expr_id), tr.get_expr_loc(expr_id));

        expr_id
    }

    fn parse_stmt_block(&mut self, mut stmt_pairs: Pairs<Rule>) -> StmtId {
        // Process the body of statements, adding them to the block as we go
        let mut stmts = Vec::new();
        while let Some(inner_pair) = stmt_pairs.next() {
            let start = inner_pair.as_span().start();
            let end = inner_pair.as_span().end();
            let stmt = match inner_pair.as_rule() {
                Rule::assign => self.parse_assign(inner_pair),
                Rule::cmd => self.parse_cmd(inner_pair),
                Rule::while_loop => self.parse_while(inner_pair),
                Rule::cond => self.parse_cond(inner_pair),
                Rule::assert_eq => self.parse_assert_eq(inner_pair),
                _ => {
                    self.handler.emit_diagnostic_parsing(
                        &format!("Unexpected rule while parsing statement block: {:?}", inner_pair.as_rule()),
                        self.fileid,
                        inner_pair,
                        Level::Error,
                    );
                    panic!();
                },
            };

            let stmt_id = self.tr.s(stmt);
            // Add the statement location to the transaction
            self.tr.add_stmt_loc(stmt_id, start, end, self.fileid);
            stmts.push(stmt_id);
        }
        self.tr.s(Stmt::Block(stmts))
    }

    fn parse_assign(&mut self, pair: pest::iterators::Pair<Rule>) -> Stmt {
        let mut inner_rules = pair.into_inner();
        let path_id_rule = inner_rules.next().unwrap();
        let expr_rule = inner_rules.next().unwrap();

        let path_id: &str = path_id_rule.as_str();

        let symbol_id = match self.st.symbol_id_from_name(path_id) {
            Some(id) => id,
            None => {
                self.handler.emit_diagnostic_parsing(&format!("Assigning to undeclared symbol: {}", path_id), self.fileid, path_id_rule, Level::Error);
                panic!();
            },
        };

        let expr_id = self.parse_expr(expr_rule.into_inner());

        Stmt::Assign(symbol_id, expr_id)
    }

    fn parse_cmd(&mut self, pair: pest::iterators::Pair<Rule>) -> Stmt {
        let mut inner_rules = pair.into_inner();
        let cmd_rule = inner_rules.next().unwrap();
        let cmd = cmd_rule.as_str();

        let arg = if let Some(expr_rule) = inner_rules.next() {
            // println!("Parsing step with expr: {}", expr_rule.as_str());
            let expr_id = self.parse_expr(expr_rule.into_inner());
            Some(expr_id)
        } else {
            None
        };

        match cmd {
            "step" => match arg {
                Some(expr_id) => Stmt::Step(expr_id),
                None => {
                    let one_expr = self.tr.e(Expr::Const(BitVecValue::from_i64(1, 2)));
                    Stmt::Step(one_expr)
                }
            },
            "fork" => {
                // if there is a passed expression, panic -- this is invalid
                if arg.is_some() {
                    self.handler.emit_diagnostic_parsing(
                        "Fork command should have no arguments.",
                        self.fileid,
                        cmd_rule,
                        Level::Error,
                    );
                    panic!();
                }
                Stmt::Fork
            }
            _ => {
                self.handler.emit_diagnostic_parsing(
                    &format!("Unexpected command: {:?}", cmd),
                    self.fileid,
                    cmd_rule,
                    Level::Error,
                );
                panic!();
            }
        }
    }

    fn parse_while(&mut self, pair: pest::iterators::Pair<Rule>) -> Stmt {
        // Parse Expression
        let mut inner_rules = pair.into_inner();
        let expr_rule = inner_rules.next().unwrap();
        let guard: ExprId = self.parse_expr(expr_rule.into_inner());

        // Parse Statement Block
        let body = self.parse_stmt_block(inner_rules);

        Stmt::While(guard, body)
    }

    fn parse_assert_eq(&mut self, pair: pest::iterators::Pair<Rule>) -> Stmt {
        let mut inner_rules = pair.into_inner();
        let lhs_rule = inner_rules.next().unwrap();
        let rhs_rule = inner_rules.next().unwrap();

        let lhs_id = self.parse_expr(lhs_rule.into_inner());
        let rhs_id = self.parse_expr(rhs_rule.into_inner());

        Stmt::AssertEq(lhs_id, rhs_id)
    }

    fn parse_cond(&mut self, pair: pest::iterators::Pair<Rule>) -> Stmt {
        let mut inner_rules = pair.into_inner();

        let if_rule = inner_rules.next().unwrap();
        let mut inner_if = if_rule.into_inner();
        let expr_rule = inner_if.next().unwrap();
        let expr_id = self.parse_expr(expr_rule.into_inner());
        let if_block = self.parse_stmt_block(inner_if);

        let else_rule = inner_rules.next().unwrap();
        let inner_else = else_rule.into_inner();
        let else_block = self.parse_stmt_block(inner_else);

        Stmt::IfElse(expr_id, if_block, else_block)
    }

    fn parse_arglist(&mut self, pair: pest::iterators::Pair<Rule>) -> Vec<Arg> {
        let mut args = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::arg => {
                    let mut arg_inner = inner_pair.into_inner();
                    let dir_pair = arg_inner.next().unwrap();
                    let id_pair = arg_inner.next().unwrap();
                    let tpe_pair = arg_inner.next().unwrap();

                    let dir = self.parse_dir(dir_pair);
                    let id = id_pair.as_str();
                    let tpe = self.parse_type(tpe_pair);

                    let symbol_id = self.st.add_without_parent(id.to_string(), tpe);
                    let arg = Arg::new(symbol_id, dir);
                    args.push(arg);
                }
                Rule::arglist => {
                    let mut nested_args = self.parse_arglist(inner_pair);
                    args.append(&mut nested_args);
                }
                _ => {
                    self.handler.emit_diagnostic_parsing(
                        &format!("Received nexpected rule while parsing arglist: {:?}", inner_pair.as_rule()),
                        self.fileid,
                        inner_pair,
                        Level::Error,
                    );
                    // FIXME: Get rid of all of these panics
                    panic!();
                },
            }
        }
        args
    }

    fn parse_fields(&mut self, pair: pest::iterators::Pair<Rule>) -> (Vec<Field>, Vec<String>) {
        let mut fields = Vec::new();
        let mut symbols = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::arg => {
                    let mut arg_inner = inner_pair.into_inner();
                    let dir_pair = arg_inner.next().unwrap();
                    let id_pair = arg_inner.next().unwrap();
                    let tpe_pair = arg_inner.next().unwrap();

                    let dir = self.parse_dir(dir_pair);
                    let id = id_pair.as_str();
                    let tpe = self.parse_type(tpe_pair);

                    let field = Field::new(id.to_string(), dir, tpe);
                    fields.push(field);
                    symbols.push(id.to_string());
                }
                Rule::arglist => {
                    let (nested_fields, nested_symbols) = self.parse_fields(inner_pair);
                    fields.extend(nested_fields);
                    symbols.extend(nested_symbols);
                }
                _ => {
                        self.handler.emit_diagnostic_parsing(
                        &format!("Unexpected rule while parsing fields: {:?}", inner_pair.as_rule()),
                        self.fileid,
                        inner_pair,
                        Level::Error,
                    );
                    panic!();
                },
            }
        }
        (fields, symbols)
    }

    fn parse_dir(&mut self, pair: pest::iterators::Pair<Rule>) -> Dir {
        match pair.as_rule() {
            Rule::dir => {
                let dir_str = pair.as_str();
                match dir_str {
                    "in" => Dir::In,
                    "out" => Dir::Out,
                    _ => {
                        
                        self.handler.emit_diagnostic_parsing(
                            &format!("Unexpected direction string: {:?}", dir_str),
                            self.fileid,
                            pair,
                            Level::Error,
                        );
                        panic!();
                    }
                }
            }
            _ => {
                self.handler.emit_diagnostic_parsing(
                    &format!("Unexpected rule while parsing direction: {:?}", pair.as_rule()),
                    self.fileid,
                    pair,
                    Level::Error,
                );
                panic!();
            }
        }
    }

    fn parse_type(&mut self, pair: pest::iterators::Pair<Rule>) -> Type {
        match pair.as_rule() {
            Rule::tpe => {
                let mut inner_rules = pair.into_inner();
                let type_str = inner_rules.next().unwrap().as_str();
                let size = type_str.parse::<u32>().unwrap();
                Type::BitVec(size)
            }
            _ => {
                self.handler.emit_diagnostic_parsing(
                    &format!("Unexpected rule while parsing type: {:?}", pair.as_rule()),
                    self.fileid,
                    pair,
                    Level::Error,
                );
                panic!();
            }
        }
    }
}

pub fn parse_file(
    filename: impl AsRef<std::path::Path>,
    handler: &mut DiagnosticHandler,
) -> Vec<(SymbolTable, Transaction)> {
    let input = std::fs::read_to_string(filename).expect("failed to load");
    let fileid = handler.add_file("func_arg_invalid.prot".to_string(), input.clone());

    let res = ProtocolParser::parse(Rule::file, &input);
    match res {
        Ok(_parsed) => {
            //println!("Parsing successful: {:?}", parsed);
        }
        Err(err) => {
            eprintln!("Parsing failed: {}", err);
            panic!("Invalid file: Failed to parse.");
        }
    }

    let pairs = ProtocolParser::parse(Rule::file, &input).unwrap();
    let inner = pairs.clone().next().unwrap().into_inner();
    let base_st: &mut SymbolTable = &mut SymbolTable::default();
    let mut trs = vec![];

    for pair in inner {
        if pair.as_rule() == Rule::struct_def {
            // dummy context to set up the symbol table with the struct; the transaction here is irrelevant
            let mut context = ParserContext { st: base_st, fileid, tr: &mut Transaction::new("".to_string()), handler };
            context.parse_struct(pair); // we don't need the struct id
        } else if pair.as_rule() == Rule::fun {
            // set up an base symbol table containing the struct, and an empty transaction for the parser to parse into
            let st = &mut base_st.clone();
            let mut tr = Transaction::new("".to_string());
            let mut context: ParserContext<'_> = ParserContext { st, fileid, tr: &mut tr, handler };
            context.parse_transaction(pair);

            trs.push((context.st.clone(), context.tr.clone()));
        }
    }
    trs
}

// Wrapper struct for custom display of pest pairs
struct DisplayPair<'i, R: pest::RuleType>(pest::iterators::Pair<'i, R>);

impl<'i, R: pest::RuleType> fmt::Display for DisplayPair<'i, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.display(f, 0)
    }
}

impl<'i, R: pest::RuleType> DisplayPair<'i, R> {
    fn display(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        let rule = self.0.as_rule();
        let span = self.0.clone().as_span();
        let text = self.0.clone().as_str();
        let indent = "  ".repeat(depth);

        // Display the rule and token matched
        if self.0.clone().into_inner().count() == 0 {
            // Leaf node (no inner rules)
            writeln!(f, "{}- {:?}: \"{}\"", indent, rule, text)?;
        } else {
            // Non-leaf node with children
            writeln!(f, "{}- {:?}", indent, rule)?;
            for pair in self.0.clone().into_inner() {
                DisplayPair(pair).display(f, depth + 1)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_re_serialize(tr: Transaction, st: SymbolTable, filename: &str) {
        println!("============= {} =============", filename);
        let mut out = Vec::new();
        serialize(&mut out, &tr, &st).unwrap();
        let out_str = String::from_utf8(out).unwrap();
        println!("{}", out_str);
        println!("======================================");
    }

    #[test]
    fn test_add_prot() {
        let filename = "tests/add_struct.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_aes128_prot() {
        let filename = "tests/aes128.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_aes128_round_prot() {
        let filename = "tests/aes128_round.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_aes128_expand_key_prot() {
        let filename = "tests/aes128_expand_key.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_mul_prot() {
        let filename = "tests/mul.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_easycond_prot() {
        let filename = "tests/cond.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_cond_prot() {
        let filename = "tests/cond.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_calyx_go_done_struct_prot() {
        let filename = "tests/calyx_go_done_struct.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    // passes the parser, but should fail typechecking
    #[test]
    fn test_invalid_step_arg() {
        let filename = "tests/invalid_step_arg.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    // Guaranteed to fail
    #[test]
    fn test_func_arg_invalid_prot() {
        let filename  = "tests/func_arg_invalid.prot";

        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_mul_ignoreprot() {
        let filename = "tests/mul_ignore.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }

    #[test]
    fn test_parse_serv_register_file() {
        let filename = "tests/serv/register_file.prot";
        let trs = parse_file(filename, &mut DiagnosticHandler::new());

        for (st, tr) in trs {
            test_re_serialize(tr, st, filename)
        }
    }
}
