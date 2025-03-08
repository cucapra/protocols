use baa::BitVecValue;
use pest::error::InputLocation;
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
    // Helper method for expected rule errors
    fn expect_rule<T>(
        &mut self,
        option: Option<T>,
        context_pair: &pest::iterators::Pair<Rule>,
        message: &str,
    ) -> Result<T, String> {
        option.ok_or_else(|| {
            let msg = message.to_string();
            self.handler.emit_diagnostic_parsing(
                &msg,
                self.fileid,
                context_pair,
                Level::Error,
            );
            msg
        })
    }

    // Helper for getting symbol id from name with error handling
    fn get_symbol_id(&mut self, name: &str, context_pair: &pest::iterators::Pair<Rule>, message: &str) -> Result<SymbolId, String> {
        self.st.symbol_id_from_name(name).ok_or_else(|| {
            let msg = format!("{}: {}", message, name);
            self.handler.emit_diagnostic_parsing(
                &msg,
                self.fileid,
                context_pair,
                Level::Error,
            );
            msg
        })
    }

    pub fn parse_boxed_expr(&mut self, pairs: Pairs<Rule>) -> Result<BoxedExpr, String> {
        PRATT_PARSER
            .map_primary(|primary| {
                let start = primary.as_span().start();
                let end = primary.as_span().end();

                match primary.as_rule() {
                    Rule::integer => {
                        let int_str = primary.as_str();
                        let int_value = int_str.parse::<i32>().unwrap();
                        let bitvec = BitVecValue::from_u64(int_value as u64, 64);
                        Ok(BoxedExpr::Const(bitvec, start, end))
                    }
                    Rule::path_id => {
                        let path_id = primary.as_str();
                        let symbol_id = self.st.symbol_id_from_name(path_id);
                        match symbol_id {
                            Some(id) => Ok(BoxedExpr::Sym(id, start, end)),
                            None => {
                                let msg = format!("Referencing undefined symbol: {}", path_id);
                                self.handler.emit_diagnostic_parsing(
                                    &msg,
                                    self.fileid,
                                    &primary,
                                    Level::Error,
                                );
                                Err(msg)
                            }
                        }
                    }
                    Rule::dont_care => Ok(BoxedExpr::DontCare(start, end)),
                    Rule::slice => {
                        let mut inner_rules = primary.clone().into_inner();
                        let path_rule = self.expect_rule(inner_rules.next(), &primary, "Expected path rule in slice expression")?;
                        let path_id = self.parse_boxed_expr(Pairs::single(path_rule))?;
                        let idx1_rule = inner_rules.next().unwrap();
                        let idx1 = idx1_rule.as_str().parse::<u32>().unwrap();
                        let idx2_rule = inner_rules.next();
                        let idx2 = match idx2_rule {
                            Some(rule) => rule.as_str().parse::<u32>().unwrap(),
                            None => idx1,
                        };
                        Ok(BoxedExpr::Slice(Box::new(path_id), idx1, idx2, start, end))
                    }
                    Rule::expr => self.parse_boxed_expr(primary.into_inner()),
                    rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
                }
            })
            .map_infix(|lhs, op, rhs| {
                let lhs_unwrap = lhs?;
                let rhs_unwrap = rhs?;
                let start = lhs_unwrap.start();
                let end = lhs_unwrap.end();
                let op = match op.as_rule() {
                    Rule::eq => BinOp::Equal,
                    Rule::log_and => BinOp::And,
                    rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
                };
                Ok(BoxedExpr::Binary(
                    op,
                    Box::new(lhs_unwrap),
                    Box::new(rhs_unwrap),
                    start,
                    end,
                ))
            })
            .map_prefix(|op, arg| {
                let arg_unwrapped = arg?;
                let start = op.as_span().start();
                let end = arg_unwrapped.end();
                let op = match op.as_rule() {
                    Rule::not => UnaryOp::Not,
                    rule => unreachable!("Expr::parse expected prefix operation, found {:?}", rule),
                };
                Ok(BoxedExpr::Unary(op, Box::new(arg_unwrapped), start, end))
            })
            .parse(pairs)
    }

    fn boxed_expr_to_expr_id(&mut self, expr: BoxedExpr) -> Result<ExprId, String> {
        let expr_id = match expr {
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
                let lhs_id = self.boxed_expr_to_expr_id(*lhs)?;
                let rhs_id = self.boxed_expr_to_expr_id(*rhs)?;
                let expr_id = self.tr.e(Expr::Binary(op, lhs_id, rhs_id));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Unary(op, arg, start, end) => {
                let arg_id = self.boxed_expr_to_expr_id(*arg)?;
                let expr_id = self.tr.e(Expr::Unary(op, arg_id));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
            BoxedExpr::Slice(expr, idx1, idx2, start, end) => {
                let sym_id = self.boxed_expr_to_expr_id(*expr)?;
                let expr_id = self.tr.e(Expr::Slice(sym_id, idx1, idx2));
                self.tr.add_expr_loc(expr_id, start, end, self.fileid);
                expr_id
            }
        };
        Ok(expr_id)
    }

    fn parse_struct(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<StructId, String> {
        let mut inner_rules = pair.clone().into_inner();
        let struct_name = self.expect_rule(inner_rules.next(), &pair, "Expected struct name")?.as_str();
        let next_rule = self.expect_rule(inner_rules.next(), &pair, "Expected fields in struct")?;
        let (pins, _symbols) = self.parse_fields(next_rule)?;
        let struct_id = self.st.add_struct(struct_name.to_string(), pins);
        Ok(struct_id)
    }

    fn parse_transaction(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<(), String> {
        match pair.as_rule() {
            Rule::fun => {
                let mut inner_rules = pair.clone().into_inner();
                let id_pair = self.expect_rule(inner_rules.next(), &pair, "Expected function identifier")?;
                let id = id_pair.as_str();
                self.tr.name = id.to_string();

                if let Some(inner_pair) = inner_rules.next() {
                    match inner_pair.as_rule() {
                        Rule::type_param => {
                            let mut type_param_rules = inner_pair.into_inner();
                            let path_id_1 = type_param_rules.next().unwrap().as_str();
                            let path_id_2 = type_param_rules.next().unwrap().as_str();
                            let struct_id = self
                                .st
                                .struct_id_from_name(path_id_2)
                                .ok_or_else(|| format!("Undefined struct: {}", path_id_2))?;
                            let dut_struct = self.st[struct_id].clone();
                            let dut_symbol_id = self
                                .st
                                .add_without_parent(path_id_1.to_string(), Type::Struct(struct_id));
                            self.tr.type_args = vec![dut_symbol_id];
                            for pin in dut_struct.pins() {
                                let pin_name = pin.name().to_string();
                                self.st.add_with_parent(pin_name, dut_symbol_id);
                            }
                        }
                        _ => {
                            let msg = format!(
                                "Attempted to parse DUT type param. Unexpected rule: {:?}",
                                inner_pair.as_rule()
                            );
                            self.handler.emit_diagnostic_parsing(
                                &msg,
                                self.fileid,
                                &inner_pair,
                                Level::Error,
                            );
                            return Err(msg);
                        }
                    }
                }

                if let Some(arglist_pair) = inner_rules.peek() {
                    if arglist_pair.as_rule() == Rule::arglist {
                        let arg_rules = self.expect_rule(inner_rules.next(), &arglist_pair, "Expected argument list")?;
                        self.tr.args = self.parse_arglist(arg_rules)?;
                    } else {
                        self.tr.args = Vec::new();
                    }
                } else {
                    self.tr.args = Vec::new();
                }

                self.tr.body = self.parse_stmt_block(inner_rules)?;
                Ok(())
            }
            _ => {
                let msg = format!(
                    "Unexpected rule while parsing transaction: {:?}",
                    pair.as_rule()
                );
                self.handler.emit_diagnostic_parsing(
                    &msg,
                    self.fileid,
                    &pair,
                    Level::Error,
                );
                Err(msg)
            }
        }
    }

    fn parse_expr(&mut self, pairs: Pairs<Rule>) -> Result<ExprId, String> {
        let boxed_expr = self.parse_boxed_expr(pairs)?;
        let expr_id = self.boxed_expr_to_expr_id(boxed_expr)?;
        Ok(expr_id)
    }

    fn parse_stmt_block(&mut self, mut stmt_pairs: Pairs<Rule>) -> Result<StmtId, String> {
        let mut stmts = Vec::new();
        while let Some(inner_pair) = stmt_pairs.next() {
            let start = inner_pair.as_span().start();
            let end = inner_pair.as_span().end();
            let stmt = match inner_pair.as_rule() {
                Rule::assign => self.parse_assign(inner_pair)?,
                Rule::cmd => self.parse_cmd(inner_pair)?,
                Rule::while_loop => self.parse_while(inner_pair)?,
                Rule::cond => self.parse_cond(inner_pair)?,
                Rule::assert_eq => self.parse_assert_eq(inner_pair)?,
                _ => {
                    let msg = format!(
                        "Unexpected rule while parsing statement block: {:?}",
                        inner_pair.as_rule()
                    );
                    self.handler.emit_diagnostic_parsing(
                        &msg,
                        self.fileid,
                        &inner_pair,
                        Level::Error,
                    );
                    return Err(msg);
                }
            };
            let stmt_id = self.tr.s(stmt);
            self.tr.add_stmt_loc(stmt_id, start, end, self.fileid);
            stmts.push(stmt_id);
        }
        Ok(self.tr.s(Stmt::Block(stmts)))
    }

    fn parse_assign(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
        let mut inner_rules = pair.clone().into_inner();
        let path_id_rule = self.expect_rule(inner_rules.next(), &pair, "Expected path identifier in assignment")?;
        let expr_rule = self.expect_rule(inner_rules.next(), &pair, "Expected expression in assignment")?;
        
        let path_id: &str = path_id_rule.as_str();
        let symbol_id = self.get_symbol_id(path_id, &path_id_rule, "Assigning to undeclared symbol")?;
        let expr_id = self.parse_expr(expr_rule.into_inner())?;
        
        Ok(Stmt::Assign(symbol_id, expr_id))
    }

    fn parse_cmd(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
        let mut inner_rules = pair.clone().into_inner();
        let cmd_rule = self.expect_rule(inner_rules.next(), &pair, "Expected command")?;
        let cmd = cmd_rule.as_str();
        
        let arg = if let Some(expr_rule) = inner_rules.next() {
            let expr_id = self.parse_expr(expr_rule.into_inner())?;
            Some(expr_id)
        } else {
            None
        };
        
        match cmd {
            "step" => match arg {
                Some(expr_id) => Ok(Stmt::Step(expr_id)),
                None => {
                    let one_expr = self.tr.e(Expr::Const(BitVecValue::from_i64(1, 2)));
                    Ok(Stmt::Step(one_expr))
                }
            },
            "fork" => {
                if arg.is_some() {
                    let msg = "Fork command should have no arguments.".to_string();
                    self.handler.emit_diagnostic_parsing(&msg, self.fileid, &cmd_rule, Level::Error);
                    return Err(msg);
                }
                Ok(Stmt::Fork)
            }
            _ => {
                let msg = format!("Unexpected command: {:?}", cmd);
                self.handler.emit_diagnostic_parsing(&msg, self.fileid, &cmd_rule, Level::Error);
                Err(msg)
            }
        }
    }

    fn parse_while(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
        let mut inner_rules = pair.clone().into_inner();
        let expr_rule = self.expect_rule(inner_rules.next(), &pair, "Expected expression in while loop")?;
        let guard = self.parse_expr(expr_rule.into_inner())?;
        let body = self.parse_stmt_block(inner_rules)?;
        Ok(Stmt::While(guard, body))
    }

    fn parse_assert_eq(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
        let mut inner_rules = pair.clone().into_inner();
        let lhs_rule = self.expect_rule(inner_rules.next(), &pair, "Expected left-hand side expression in assert_eq")?;
        let rhs_rule = self.expect_rule(inner_rules.next(), &pair, "Expected right-hand side expression in assert_eq")?;
        let lhs_id = self.parse_expr(lhs_rule.into_inner())?;
        let rhs_id = self.parse_expr(rhs_rule.into_inner())?;
        Ok(Stmt::AssertEq(lhs_id, rhs_id))
    }

    fn parse_cond(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
        let mut inner_rules = pair.clone().into_inner();
        let if_rule = self.expect_rule(inner_rules.next(), &pair, "Expected if condition")?;
        let mut inner_if = if_rule.into_inner();
        let expr_rule = self.expect_rule(inner_if.next(), &pair, "Expected expression in if condition")?;
        let expr_id = self.parse_expr(expr_rule.into_inner())?;
        let if_block = self.parse_stmt_block(inner_if)?;
        let else_rule = self.expect_rule(inner_rules.next(), &pair, "Expected else block")?;
        let inner_else = else_rule.into_inner();
        let else_block = self.parse_stmt_block(inner_else)?;
        Ok(Stmt::IfElse(expr_id, if_block, else_block))
    }

    fn parse_arglist(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Vec<Arg>, String> {
        let mut args = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::arg => {
                    let mut arg_inner = inner_pair.clone().into_inner();
                    let dir_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected direction in argument")?;
                    let id_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected identifier in argument")?;
                    let tpe_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected type in argument")?;
                    let dir = self.parse_dir(dir_pair)?;
                    let id = id_pair.as_str();
                    let tpe = self.parse_type(tpe_pair)?;
                    let symbol_id = self.st.add_without_parent(id.to_string(), tpe);
                    let arg = Arg::new(symbol_id, dir);
                    args.push(arg);
                }
                Rule::arglist => {
                    let mut nested_args = self.parse_arglist(inner_pair)?;
                    args.append(&mut nested_args);
                }
                _ => {
                    let msg = format!(
                        "Received unexpected rule while parsing arglist: {:?}",
                        inner_pair.as_rule()
                    );
                    self.handler.emit_diagnostic_parsing(
                        &msg,
                        self.fileid,
                        &inner_pair,
                        Level::Error,
                    );
                    return Err(msg);
                }
            }
        }
        Ok(args)
    }

    fn parse_fields(
        &mut self,
        pair: pest::iterators::Pair<Rule>,
    ) -> Result<(Vec<Field>, Vec<String>), String> {
        let mut fields = Vec::new();
        let mut symbols = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::arg => {
                    let mut arg_inner = inner_pair.clone().into_inner();
                    let dir_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected direction in field")?;
                    let id_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected identifier in field")?;
                    let tpe_pair = self.expect_rule(arg_inner.next(), &inner_pair, "Expected type in field")?;
                    let dir = self.parse_dir(dir_pair)?;
                    let id = id_pair.as_str();
                    let tpe = self.parse_type(tpe_pair)?;
                    let field = Field::new(id.to_string(), dir, tpe);
                    fields.push(field);
                    symbols.push(id.to_string());
                }
                Rule::arglist => {
                    let (nested_fields, nested_symbols) = self.parse_fields(inner_pair)?;
                    fields.extend(nested_fields);
                    symbols.extend(nested_symbols);
                }
                _ => {
                    let msg = format!(
                        "Unexpected rule while parsing fields: {:?}",
                        inner_pair.as_rule()
                    );
                    self.handler.emit_diagnostic_parsing(
                        &msg,
                        self.fileid,
                        &inner_pair,
                        Level::Error,
                    );
                    return Err(msg);
                }
            }
        }
        Ok((fields, symbols))
    }

    fn parse_dir(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Dir, String> {
        match pair.as_rule() {
            Rule::dir => {
                let dir_str = pair.as_str();
                match dir_str {
                    "in" => Ok(Dir::In),
                    "out" => Ok(Dir::Out),
                    _ => {
                        let msg = format!("Unexpected direction string: {:?}", dir_str);
                        self.handler
                            .emit_diagnostic_parsing(&msg, self.fileid, &pair, Level::Error);
                        Err(msg)
                    }
                }
            }
            _ => {
                let msg = format!(
                    "Unexpected rule while parsing direction: {:?}",
                    pair.as_rule()
                );
                self.handler
                    .emit_diagnostic_parsing(&msg, self.fileid, &pair, Level::Error);
                Err(msg)
            }
        }
    }

    fn parse_type(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Type, String> {
        match pair.as_rule() {
            Rule::tpe => {
                let mut inner_rules = pair.into_inner();
                let type_str = inner_rules.next().unwrap().as_str();
                let size = type_str.parse::<u32>().unwrap();
                Ok(Type::BitVec(size))
            }
            _ => {
                let msg = format!("Unexpected rule while parsing type: {:?}", pair.as_rule());
                self.handler
                    .emit_diagnostic_parsing(&msg, self.fileid, &pair, Level::Error);
                Err(msg)
            }
        }
    }
}

pub fn parse_file(
    filename: impl AsRef<std::path::Path>,
    handler: &mut DiagnosticHandler,
) -> Result<Vec<(SymbolTable, Transaction)>, String> {
    let name = filename.as_ref().to_str().unwrap().to_string();
    let input = std::fs::read_to_string(filename).map_err(|e| format!("failed to load: {}", e))?;
    let fileid = handler.add_file(name, input.clone());

    let res = ProtocolParser::parse(Rule::file, &input);
    match res {
        Ok(_parsed) => {
            //println!("Parsing successful: {:?}", parsed);
        }
        Err(err) => {
            let (start, end) = match err.location {
                InputLocation::Pos(start) => (start, start),
                InputLocation::Span(span) => span,
            };
            let msg: String = format!("Lexing failed: {}", err.variant.message());
            handler.emit_diagnostic_lexing(&msg, fileid, start, end, Level::Error);
            return Err(msg);
        }
    }

    let pairs = ProtocolParser::parse(Rule::file, &input).unwrap();
    let inner = pairs.clone().next().unwrap().into_inner();
    let base_st: &mut SymbolTable = &mut SymbolTable::default();
    let mut trs = vec![];

    for pair in inner {
        if pair.as_rule() == Rule::struct_def {
            // dummy context to set up the symbol table with the struct; the transaction here is irrelevant
            let mut context = ParserContext {
                st: base_st,
                fileid,
                tr: &mut Transaction::new("".to_string()),
                handler,
            };
            if let Err(e) = context.parse_struct(pair) {
                let msg = format!("Error parsing struct: {}", e);
                eprintln!("{}", msg);
                return Err(msg);
            }
        } else if pair.as_rule() == Rule::fun {
            // set up an base symbol table containing the struct, and an empty transaction for the parser to parse into
            let st = &mut base_st.clone();
            let mut tr = Transaction::new("".to_string());
            let mut context: ParserContext<'_> = ParserContext {
                st,
                fileid,
                tr: &mut tr,
                handler,
            };
            if let Err(e) = context.parse_transaction(pair) {
                return Err(e);
            }

            trs.push((context.st.clone(), context.tr.clone()));
        }
    }
    Ok(trs)
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
    // All tests moved to serialize.rs
}