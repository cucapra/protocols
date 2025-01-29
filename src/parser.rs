// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use pest::Parser;
use pest_derive::Parser;
use pest::pratt_parser::PrattParser;
use pest::iterators::Pairs;
use std::{fmt, process::id, vec};
use baa::BitVecValue;

use crate::{ir::*};

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

pub fn parse_expr(pairs: Pairs<Rule>, tr: &mut Transaction, st : &mut SymbolTable) ->  ExprId {
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {

            // parse integer literals
            Rule::integer => {
                let int_str = primary.as_str();
                let int_value = int_str.parse::<i32>().unwrap();
                // FIXME: Is this the correct way to convert?
                let bitvec = BitVecValue::from_u64(int_value as u64, 32);
                tr.e(Expr::Const(bitvec))
            }

            // parse path identifiers
            Rule::path_id => {
                let path_id = primary.as_str();
                let symbol_id = SymbolTable::symbol_id_from_name(st, path_id);
                match symbol_id {
                    Some(id) => tr.e(Expr::Sym(id)),
                    None => panic!("Referencing undefined symbol: {}", path_id),
                }
            }

            // if primary is an expression (due to parens), recursively parse its inner constituents
            Rule::expr => parse_expr(primary.into_inner(), tr, st),
            rule => unreachable!("Expr::parse expected atom, found {:?}", rule)
        })

        // FIXME: two closures require unique access to `*tr` at the same time
        // Parse binary expressions
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::eq => BinOp::Equal,
                Rule::log_and => BinOp::And,
                rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
            };
            let bin_expression = Expr::Binary(
                op,
                lhs,
                rhs
            );
            tr.e(bin_expression)
        })

        // Parse unary expressions
        .map_prefix(|op, arg| {
            let op = match op.as_rule() {
                Rule::not => UnaryOp::Not,
                rule => unreachable!("Expr::parse expected prefix operation, found {:?}", rule),
            };
            let unary_expression = Expr::Unary(op, arg);
            tr.e(unary_expression)
        })
        .parse(pairs)
}


// fn build_ir(pair: pest::iterators::Pair<Rule>) -> (Transaction, SymbolTable) {
//     match pair.as_rule() {
//         Rule::file => {
//             let mut inner_rules = pair.into_inner();
//             let mut symbol_table = SymbolTable::default();
//             let mut transactions = Vec::new();

//             while let Some(inner_pair) = inner_rules.next() {
//                 match inner_pair.as_rule() {
//                     Rule::fun => {
//                         let transaction = build_transaction(inner_pair);
//                         transactions.push(transaction);
//                     }
//                     _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
//                 }
//             }

//             let transaction = if transactions.len() == 1 {
//                 transactions.into_iter().next().unwrap()
//             } else {
//                 panic!("Expected exactly one transaction, found {}", transactions.len());
//             };

//             (transaction, symbol_table)
//         }
//         _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
//     }
// }

fn build_struct(pair : pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> StructId {
    let mut inner_rules = pair.into_inner();
    let struct_id = inner_rules.next().unwrap().as_str();

    let pins = build_fields(inner_rules.next().unwrap(), st);

    st.add_struct(struct_id.to_string(), pins)
}

fn build_transaction(pair: pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> Transaction {
    match pair.as_rule() {
        Rule::fun => {
            let mut inner_rules = pair.into_inner();
            let id_pair = inner_rules.next().unwrap();
            let id = id_pair.as_str();
            let mut tr = Transaction::new(id.to_string());
            tr.args = build_arglist(inner_rules.next().unwrap(), st);

            // Process the body of statements, adding them to the block as we go
            while let Some(inner_pair) = inner_rules.next() {
                match inner_pair.as_rule() {
                    Rule::assign => {
                        let stmt = parse_assign(inner_pair, tr, st);
                        tr.s(stmt);
                    }
                    Rule::cmd => {
                        let stmt = parse_cmd(inner_pair, tr, st);
                        tr.s(stmt);
                    }
                    Rule::while_loop => {
                        let stmt = parse_while(inner_pair, tr, st);
                        tr.s(stmt);
                    }
                    Rule::cond => {
                        let stmt = parse_cond(inner_pair, tr, st);
                        tr.s(stmt);
                    }
                    _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
                }
            }
            println!("Transaction: {:?}", tr);
            tr
        }
        _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

fn parse_assign(pair: pest::iterators::Pair<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    let path_id_rule = pair.into_inner().next().unwrap();
    let expr_rule = pair.into_inner().next().unwrap();

    let path_id = path_id_rule.as_str();
    // TODO: Error handling
    let symbol_id = match st.symbol_id_from_name(path_id) {
        Some(id) => id,
        None => panic!("Assigning to undeclared symbol: {}", path_id),
    };

    let expr_id = parse_expr(expr_rule.into_inner(), tr, st);

    // Dummy implementation
    Stmt::Assign(symbol_id, expr_id)
}

fn parse_cmd(pair: pest::iterators::Pair<Rule>, st: &mut SymbolTable) -> Stmt {
    let cmd=  pair.as_str();
    match cmd {
        "step" => Stmt::Step,
        "fork" => Stmt::Fork,
        _ => panic!("Unexpected command: {:?}", cmd),
    }
}

fn parse_while(pair: pest::iterators::Pair<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    // Parse Expression
    let mut inner_rules = pair.into_inner();
    let expr_rule = inner_rules.next().unwrap();
    let guard: ExprId = parse_expr(expr_rule.into_inner(), tr, st);

    // Parse Statement Block
    let body = parse_stmt_block(inner_rules, tr, st);

    Stmt::While(guard, body)
}

fn parse_stmt_block(stmt_pairs: Pairs<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> StmtId {
    // Parse Statement Block. FIXME: Duplicate code.
    // Process the body of statements, adding them to the block as we go
    let stmts = Vec::new();
    while let Some(inner_pair) = stmt_pairs.next() {
        match inner_pair.as_rule() {
            Rule::assign => {
                let stmt = parse_assign(inner_pair, tr, st);
                stmts.push(tr.s(stmt));
            }
            Rule::cmd => {
                let stmt = parse_cmd(inner_pair,tr, st);
                stmts.push(tr.s(stmt));
            }
            Rule::while_loop => {
                let stmt = parse_while(inner_pair,tr, st);
                stmts.push(tr.s(stmt));
            }
            Rule::cond => {
                let stmt = parse_cond(inner_pair, tr, st);
                stmts.push(tr.s(stmt));
            }
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    tr.s(Stmt::Block(stmts))
}

fn parse_cond(pair: pest::iterators::Pair<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    // Dummy implementation
    let mut inner_rules = pair.into_inner();

    let if_rule = inner_rules.next().unwrap();
    let inner_if = if_rule.into_inner();
    let expr_rule = inner_if.next().unwrap();
    let expr_id = parse_expr(expr_rule.into_inner(), tr, st);
    let if_block = parse_stmt_block(inner_if, tr, st);

    let else_rule = inner_rules.next().unwrap();
    let inner_else = else_rule.into_inner();
    let else_block = parse_stmt_block(inner_else, tr, st);

    Stmt::IfElse(expr_id, if_block, else_block)
    
}

fn build_arglist(pair : pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> Vec<Arg> {
    let mut args = Vec::new();
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::arg => {
                let mut arg_inner = inner_pair.into_inner();
                let dir_pair = arg_inner.next().unwrap();
                let id_pair = arg_inner.next().unwrap();
                let tpe_pair = arg_inner.next().unwrap();

                let dir = parse_dir(dir_pair);
                let id = id_pair.as_str();
                let tpe = parse_type(tpe_pair);

                let symbol_id = st.add_without_parent(id.to_string(), tpe);
                let arg = Arg::new(symbol_id, dir);
                args.push(arg);
            }
            Rule::arglist => {
                let mut nested_args = build_arglist(inner_pair, st);
                args.append(&mut nested_args);
            }
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    args
}

fn build_fields(pair : pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> Vec<Field> {
    let mut fields = Vec::new();
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::arg => {
                let mut arg_inner = inner_pair.into_inner();
                let dir_pair = arg_inner.next().unwrap();
                let id_pair = arg_inner.next().unwrap();
                let tpe_pair = arg_inner.next().unwrap();

                let dir = parse_dir(dir_pair);
                let id = id_pair.as_str();
                let tpe = parse_type(tpe_pair);

                let field = Field::new(id.to_string(), dir, tpe);
                fields.push(field);
            }
            Rule::arglist => {
                let mut nested_fields = build_fields(inner_pair, st);
                fields.append(&mut nested_fields);
            }
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    fields
}

fn parse_dir(pair : pest::iterators::Pair<Rule>) -> Dir {
    match pair.as_rule() {
        Rule::dir => {
            let dir_str = pair.as_str();
            match dir_str {
                "in" => Dir::In,
                "out" => Dir::Out,
                _ => panic!("Unexpected direction string: {:?}", dir_str),
            }
        }
        _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Type {
    match pair.as_rule() {
        Rule::tpe => {
            let type_str = pair.as_str();
            match type_str {
                "u32" => Type::BitVec(32),
                "u1" => Type::BitVec(1),
                _ => panic!("Unexpected type string: {:?}", type_str),
            }
        }
        _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
    }
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

    fn parse_file(filename: impl AsRef<std::path::Path>) {
        let input = std::fs::read_to_string(filename).expect("failed to load");
        let res = ProtocolParser::parse(Rule::file, &input);
        match res {
            Ok(parsed) => {
                println!("Parsing successful: {:?}", parsed); 
            },
            Err(err) => {
                eprintln!("Parsing failed: {}", err);
                panic!("failed to parse");
            }
        }

        let pairs = ProtocolParser::parse(Rule::file, &input).unwrap();
        // first (and only) pair in pairs is always file
        if let Some(first_pair) = pairs.clone().next() {
            // println!("First pair rule: {:?}", first_pair.as_rule());
        }
        // println!("Length of pairs: {}", pairs.clone().count());
        let inner = pairs.clone().next().unwrap().into_inner();
        let mut st: &mut SymbolTable = &mut SymbolTable::default();
        for pair in inner {
            if pair.as_rule() == Rule::struct_def {
                let _parsed_struct = build_struct(pair, st);
                // println!("Struct: {:?}", struct.name);
            }
            else if pair.as_rule() == Rule::fun {
                let _tr = build_transaction(pair, st);
                // println!("Transaction: {:?}", transaction.name);
            }
        }
        // let pair = pairs.into_inner();
        // let (transaction, symbol_table) = build_ir(pair);
    }

    #[test]
    fn test_add_prot() {
        parse_file("tests/add.prot");
    }

    #[test]
    fn test_calyx_go_done_prot() {
        parse_file("tests/calyx_go_done.prot");
    }

    #[test]
    fn test_mul_prot() {
        parse_file("tests/mul.prot");
    }

    #[test]
    fn test_easycond_prot() {
        parse_file("tests/cond.prot");
    }

    #[test]
    fn test_cond_prot() {
        parse_file("tests/cond.prot");
    }

    #[test]
    fn test_calyx_go_done_struct_prot() {
        parse_file("tests/calyx_go_done_struct.prot");
    }
}
