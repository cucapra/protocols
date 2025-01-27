// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use pest::Parser;
use pest_derive::Parser;
use pest::pratt_parser::PrattParser;
use pest::iterators::Pairs;
use std::fmt;
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

// pub fn parse_expr(pairs: Pairs<Rule>) ->  Expr {
//     PRATT_PARSER
//         .map_primary(|primary| match primary.as_rule() {
//             Rule::integer => {
//                 let int_str = primary.as_str();
//                 let int_value = int_str.parse::<i32>().unwrap();
//                 // FIXME: Is this the correct way to convert?
//                 let bitvec = BitVecValue::from_u64(int_value as u64, 32);
//                 Expr::Const(bitvec)
//             }
//             // if primary is an expression (due to parens), recursively parse its inner constituents
//             Rule::expr => parse_expr(primary.into_inner()),
//             rule => unreachable!("Expr::parse expected atom, found {:?}", rule)
//         })
//         .map_infix(|lhs, op, rhs| {
//             let op = match op.as_rule() {
//                 Rule::eq => BinOp::Equal,
//                 Rule::log_and => BinOp::And,
//                 rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
//             };
//             Expr::Binary {
//                 op,
//                 lhs: lhs.
//                 rhs: Box::new(rhs),
//             }
//         })
//         .map_prefix(|op, arg| {
//             let op = match op.as_rule() {
//                 Rule::negate => UnaryOperator::Negate,
//                 rule => unreachable!("Expr::parse expected prefix operation, found {:?}", rule),
//             };
//             Expr::UnaryOp {arg: Box::new(arg) , op: op }
//         })
//         .parse(pairs)
// }
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

fn build_transaction(pair: pest::iterators::Pair<Rule>, sym : &mut SymbolTable) -> Transaction {
    match pair.as_rule() {
        Rule::fun => {
            let mut inner_rules = pair.into_inner();
            let id_pair = inner_rules.next().unwrap();
            let id = id_pair.as_str();
            let mut trans = Transaction::new(id.to_string());
            trans.args = build_arglist(inner_rules.next().unwrap(), sym);
            // Process the rest of the inner rules if needed
            for inner_pair in inner_rules {
                // Handle other inner pairs
            }
            trans
        }
        _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

fn build_arglist(pair : pest::iterators::Pair<Rule>, sym : &mut SymbolTable) -> Vec<Arg> {
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

                let symbol_id = sym.add_without_parent(id.to_string(), tpe);
                let arg = Arg::new(symbol_id, dir);
                args.push(arg);
            }
            Rule::arglist => {
                let mut nested_args = build_arglist(inner_pair, sym);
                args.append(&mut nested_args);
            }
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    args
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
        for pair in inner {
            if pair.as_rule() == Rule::fun {
                let mut sym = &mut SymbolTable::default();
                let mut transaction = build_transaction(pair, sym);
                println!("Transaction: {:?}", transaction.name);
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
