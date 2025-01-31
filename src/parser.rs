// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>

use pest::Parser;
use pest_derive::Parser;
use pest::pratt_parser::PrattParser;
use pest::iterators::Pairs;
use std::{fmt, process::id, vec, io::stdout};
use baa::BitVecValue;

use crate::{ir::*, serialize::serialize};

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


pub fn parse_boxed_expr(pairs: Pairs<Rule>, _tr: &mut Transaction, st : &mut SymbolTable) ->  BoxedExpr {
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {

            // parse integer literals
            Rule::integer => {
                let int_str = primary.as_str();
                let int_value = int_str.parse::<i32>().unwrap();
                // FIXME: Is this the correct way to convert?
                let bitvec = BitVecValue::from_u64(int_value as u64, 1);
                BoxedExpr::Const(bitvec)
            }

            // parse path identifiers
            Rule::path_id => {
                let path_id = primary.as_str();
                // FIXME: Use 
                let symbol_id = SymbolTable::symbol_id_from_name(st, path_id);
                match symbol_id {
                    Some(id) => BoxedExpr::Sym(id),
                    None => panic!("Referencing undefined symbol: {}", path_id),
                }
            }

            // parse don't care
            Rule::dont_care => BoxedExpr::DontCare,

            // if primary is an expression (due to parens), recursively parse its inner constituents
            Rule::expr => parse_boxed_expr(primary.into_inner(), _tr, st),
            rule => unreachable!("Expr::parse expected atom, found {:?}", rule)
        })

        // Parse binary expressions
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::eq => BinOp::Equal,
                Rule::log_and => BinOp::And,
                rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
            };
            BoxedExpr::Binary(
                op,
                Box::new(lhs),
                Box::new(rhs)
            )
        })

        // Parse unary expressions
        .map_prefix(|op, arg| {
            let op = match op.as_rule() {
                Rule::not => UnaryOp::Not,
                rule => unreachable!("Expr::parse expected prefix operation, found {:?}", rule),
            };
            BoxedExpr::Unary(op, Box::new(arg))
        })
        .parse(pairs)
}

fn boxed_expr_to_expr_id(expr: BoxedExpr, tr: &mut Transaction, st: &mut SymbolTable) -> ExprId {
    match expr {
        BoxedExpr::Const(value) => tr.e(Expr::Const(value)),
        BoxedExpr::Sym(symbol_id) => tr.e(Expr::Sym(symbol_id)),
        BoxedExpr::DontCare => tr.e(Expr::DontCare),
        BoxedExpr::Binary(op, lhs, rhs) => {
            let lhs_id = boxed_expr_to_expr_id(*lhs, tr, st);
            let rhs_id = boxed_expr_to_expr_id(*rhs, tr, st);
            tr.e(Expr::Binary(op, lhs_id, rhs_id))
        }
        BoxedExpr::Unary(op, arg) => {
            let arg_id = boxed_expr_to_expr_id(*arg, tr, st);
            tr.e(Expr::Unary(op, arg_id))
        }
    }
}

fn parse_struct(pair : pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> StructId {
    let mut inner_rules = pair.into_inner();
    let struct_name = inner_rules.next().unwrap().as_str();

    let (pins, symbols) = parse_fields(inner_rules.next().unwrap(), st);
    let struct_id = st.add_struct(struct_name.to_string(), pins);

    struct_id
}

// TODO: Add line numbers and character loc. 
fn parse_transaction(pair: pest::iterators::Pair<Rule>, st :  &mut SymbolTable) -> Transaction {
    match pair.as_rule() {
        Rule::fun => {
            let mut inner_rules = pair.into_inner();
            let id_pair = inner_rules.next().unwrap();
            let id = id_pair.as_str();
            let mut tr = Transaction::new(id.to_string());
            

            // Parse the DUT definiton
            if let Some(inner_pair) = inner_rules.next() {
                match inner_pair.as_rule() {
                    Rule::type_param => {
                        let mut type_param_rules = inner_pair.into_inner();
                        let path_id_1 = type_param_rules.next().unwrap().as_str();
                        let path_id_2 = type_param_rules.next().unwrap().as_str();
                        
                            let adder_struct_id = {
                                let struct_id = st.struct_id_from_name(path_id_2)
                                    .expect(&format!("Undefined struct: {}", path_id_2));
                                struct_id
                            };
    
                            let adder_struct = {
                                let struct_ref = st.struct_from_struct_id(adder_struct_id);
                                struct_ref.clone() // Clone if necessary to avoid borrowing issues
                            };
    
                            let dut_symbol_id = st.add_without_parent(path_id_1.to_string(), Type::Struct(adder_struct_id));
    
                            for pin in adder_struct.pins() {
                                let pin_name = pin.name().to_string();
                                st.add_with_parent(pin_name, dut_symbol_id);
                            }

                    }
                    _ => panic!("Attempted to parse DUT type param. Unexpected rule: {:?}", inner_pair.as_rule()),
                }
            }

            tr.args = parse_arglist(inner_rules.next().unwrap(), st);

            // Process the body of statements, adding them to the block as we go
            tr.body = parse_stmt_block(inner_rules, &mut tr, st);
            tr
        }
        _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
    }
}

fn parse_expr(pairs: Pairs<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> ExprId {
    let boxed_expr = parse_boxed_expr(pairs, tr, st);
    let expr_id = boxed_expr_to_expr_id(boxed_expr, tr, st);
    expr_id
    // tr.e(Expr::Const(BitVecValue::from_u64(0, 32)))
}  

fn parse_assign(pair: pest::iterators::Pair<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    let mut inner_rules = pair.into_inner();
    let path_id_rule = inner_rules.next().unwrap();
    let expr_rule = inner_rules.next().unwrap();

    let path_id = path_id_rule.as_str();

    let symbol_id = match st.symbol_id_from_name(path_id) {
        Some(id) => id,
        None => panic!("Assigning to undeclared symbol: {}", path_id),
    };

    let expr_id = parse_expr(expr_rule.into_inner(), tr, st);

    Stmt::Assign(symbol_id, expr_id)
}

fn parse_cmd(pair: pest::iterators::Pair<Rule>, _tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    let mut inner_rules = pair.into_inner();
    let cmd_rule = inner_rules.next().unwrap();
    let cmd = cmd_rule.as_str();
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

fn parse_stmt_block(mut stmt_pairs: Pairs<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> StmtId {
    // Parse Statement Block. FIXME: Duplicate code.
    // Process the body of statements, adding them to the block as we go
    let mut stmts = Vec::new();
    while let Some(inner_pair) = stmt_pairs.next() {
        let stmt = match inner_pair.as_rule() {
            Rule::assign => parse_assign(inner_pair, tr, st),
            Rule::cmd => parse_cmd(inner_pair, tr, st),
            Rule::while_loop => parse_while(inner_pair, tr, st),
            Rule::cond => parse_cond(inner_pair, tr, st),
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        };
        stmts.push(tr.s(stmt));
    }
    tr.s(Stmt::Block(stmts))
}

fn parse_cond(pair: pest::iterators::Pair<Rule>, tr: &mut Transaction, st: &mut SymbolTable) -> Stmt {
    // Dummy implementation
    let mut inner_rules = pair.into_inner();

    let if_rule = inner_rules.next().unwrap();
    let mut inner_if = if_rule.into_inner();
    let expr_rule = inner_if.next().unwrap();
    let expr_id = parse_expr(expr_rule.into_inner(), tr, st);
    let if_block = parse_stmt_block(inner_if, tr, st);

    let else_rule = inner_rules.next().unwrap();
    let inner_else = else_rule.into_inner();
    let else_block = parse_stmt_block(inner_else, tr, st);

    Stmt::IfElse(expr_id, if_block, else_block)
    
}

fn parse_arglist(pair : pest::iterators::Pair<Rule>, st : &mut SymbolTable) -> Vec<Arg> {
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
                let mut nested_args = parse_arglist(inner_pair, st);
                args.append(&mut nested_args);
            }
            _ => panic!("In parse_arglist. Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    args
}

fn parse_fields(pair: pest::iterators::Pair<Rule>, st: &mut SymbolTable) -> (Vec<Field>, Vec<String>) {
    let mut fields = Vec::new();
    let mut symbols = Vec::new();
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
                symbols.push(id.to_string());
            }
            Rule::arglist => {
                let (nested_fields, nested_symbols) = parse_fields(inner_pair, st);
                fields.extend(nested_fields);
                symbols.extend(nested_symbols);
            }
            _ => panic!("Unexpected rule: {:?}", inner_pair.as_rule()),
        }
    }
    (fields, symbols)
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
            let mut inner_rules = pair.into_inner();
            let type_str = inner_rules.next().unwrap().as_str();
            let size = type_str.parse::<u32>().unwrap();
            Type::BitVec(size)
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

    fn parse_file(filename: impl AsRef<std::path::Path>) -> (Transaction, SymbolTable) {
        let input = std::fs::read_to_string(filename).expect("failed to load");
        let res = ProtocolParser::parse(Rule::file, &input);
        match res {
            Ok(_parsed) => {
                //println!("Parsing successful: {:?}", parsed); 
            },
            Err(err) => {
                eprintln!("Parsing failed: {}", err);
                panic!("Invalid file: Failed to parse.");
            }
        }

        let pairs = ProtocolParser::parse(Rule::file, &input).unwrap();
        // first (and only) pair in pairs is always file
        if let Some(_first_pair) = pairs.clone().next() {
            // println!("First pair rule: {:?}", first_pair.as_rule());
        }
        // println!("Length of pairs: {}", pairs.clone().count());
        let inner = pairs.clone().next().unwrap().into_inner();
        let st: &mut SymbolTable = &mut SymbolTable::default();
        let mut tr =  Transaction::new("dummy".to_string());
        for pair in inner {
            if pair.as_rule() == Rule::struct_def {
                let _parsed_struct = parse_struct(pair, st);
                // println!("Struct: {:?}", struct.name);
            }
            else if pair.as_rule() == Rule::fun {
                tr = parse_transaction(pair, st);
            }
        }

        (tr, st.clone())
    }

    fn test_re_serialize(tr: Transaction, st : SymbolTable, filename: &str) {
        println!("Transaction {:?}: {:?}", tr.name, tr);
        println!("============= {} =============", filename);

        // Serialize into a string first, and then use println macro; 
        // else, cargo test seems to display in the wrong order
        let mut out = Vec::new();
        serialize(&mut out, &tr, &st).unwrap();
        let out_str = String::from_utf8(out).unwrap();
        println!("{}", out_str);

        println!("======================================");
    }

    #[test]
    fn test_add_prot() {
        let filename = "tests/add_struct.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    #[test]
    fn test_aes128_prot() {
        let filename = "tests/aes128.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    #[test]
    fn test_mul_prot() {
        let filename = "tests/mul.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    #[test]
    fn test_easycond_prot() {
        let filename = "tests/cond.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    #[test]
    fn test_cond_prot() {
        let filename = "tests/cond.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    #[test]
    fn test_calyx_go_done_struct_prot() {
        let filename  = "tests/calyx_go_done_struct.prot";
        let (tr, st) = parse_file(filename);
        test_re_serialize(tr, st, filename)
    }

    // Guaranteed to fail
    // #[test]
    // fn test_func_arg_invalid_prot() {
    //     let filename  = "tests/func_arg_invalid.prot";
    //     let (tr, st) = parse_file(filename);
    //     test_re_serialize(tr, st, filename)
    // }
}
