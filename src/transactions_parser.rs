use crate::ir::Type;
use crate::scheduler::TodoItem;
use crate::{diagnostic::*, setup::bv};
use baa::BitVecValue;
use pest::{Parser, error::InputLocation, iterators::Pair};
use pest_derive::Parser;
use std::collections::HashMap;

#[derive(Parser)]
#[grammar = "transactions.pest"]
struct TransactionsParser;

/// Parses a transaction file (specified at `filepath`) using a particular `DiagnosticHandler`.
/// The argument `transaction_arg_types` maps a transaction's name to its argument types.
pub fn parse_transactions_file(
    filepath: impl AsRef<std::path::Path>,
    handler: &mut DiagnosticHandler,
    transaction_arg_types: HashMap<String, Vec<Type>>,
) -> Result<Vec<TodoItem>, String> {
    let filename = filepath.as_ref().to_str().unwrap().to_string();
    let input = std::fs::read_to_string(filepath).map_err(|e| format!("failed to load: {}", e))?;
    let fileid = handler.add_file(filename, input.clone());

    let parse_result = TransactionsParser::parse(Rule::file, &input);

    // Handle lexing errors
    if let Err(err) = parse_result {
        let (start, end) = match err.location {
            InputLocation::Pos(start) => (start, start),
            InputLocation::Span(span) => span,
        };
        let msg = format!("Lexing failed: {}", err.variant.message());
        handler.emit_diagnostic_lexing(&msg, fileid, start, end, Level::Error);
        return Err(msg);
    }

    // Access the `Rule`s contained within the parsed result
    let inner_rules = parse_result.unwrap().next().unwrap().into_inner();
    let mut todos = vec![];

    // Parse each transaction
    for transaction_pair in inner_rules {
        if let Rule::transaction = transaction_pair.as_rule() {
            let mut transaction_inner = transaction_pair.into_inner();

            // First element should be the function name (ident)
            let function_name = transaction_inner.next().unwrap().as_str().to_string();

            let arg_types = transaction_arg_types
                .get(&function_name)
                .expect("Unable to fetch argument types for transaction");

            // Parse arguments if they exist
            let mut args: Vec<BitVecValue> = vec![];
            if let Some(arglist_pair) = transaction_inner.next() {
                if arglist_pair.as_rule() == Rule::arglist {
                    args = parse_arglist(arglist_pair, handler, fileid, arg_types)?;
                }
            }

            todos.push((function_name, args));
        }
    }

    Ok(todos)
}

/// Parses a list of arguments that are supplied to a transaction,
/// returning a `Vec<BitVecValue>`
/// Arguments:
/// - `arglist_pair` is a `Pair` produced by the parser derived by Pest
/// - `handler` is the handler for emitting error diagnostics
/// - `fileid`: file descriptor
/// - `arg_types`: Slice containing the expected type of each argument
fn parse_arglist(
    arglist_pair: Pair<Rule>,
    handler: &mut DiagnosticHandler,
    fileid: usize,
    arg_types: &[Type],
) -> Result<Vec<BitVecValue>, String> {
    let mut args = vec![];

    let arg_pairs = collect_arg_pairs(arglist_pair);

    // Check that the no. of arguments supplied matches the type
    if arg_pairs.len() != arg_types.len() {
        let msg = format!(
            "Expected {} arguments but found {}",
            arg_types.len(),
            arg_pairs.len()
        );
        // Use the first arg `Pair` as the location of the error
        if let Some(first_arg) = arg_pairs.first() {
            handler.emit_diagnostic_parsing(&msg, fileid, first_arg, Level::Error);
        }
        return Err(msg);
    }

    for (arg_pair, ty) in arg_pairs.iter().zip(arg_types.iter()) {
        let arg_value = parse_arg(arg_pair, ty, handler, fileid)?;
        args.push(arg_value);
    }
    Ok(args)
}

/// Helper function to collect all arg pairs from the recursive arglist structure
fn collect_arg_pairs(arglist_pair: Pair<Rule>) -> Vec<Pair<Rule>> {
    let mut args = vec![];
    for inner_pair in arglist_pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::arg => {
                args.push(inner_pair);
            }
            Rule::arglist => {
                // Recursively collect from nested arglist
                let mut nested_args = collect_arg_pairs(inner_pair);
                args.append(&mut nested_args);
            }
            _ => {
                // Skip other rules like commas
                continue;
            }
        }
    }

    args
}

/// Parses one single argument to a transaction, returning a `BitVecValue`
/// Arguments:
/// - `arg_pair` is a `Pair` produced by the parser derived by Pest
/// - `ty`: The expected type of the argument
/// - `handler` is the handler for emitting error diagnostics
/// - `fileid`: file descriptor
fn parse_arg(
    arg_pair: &Pair<Rule>,
    ty: &Type,
    handler: &mut DiagnosticHandler,
    fileid: usize,
) -> Result<BitVecValue, String> {
    let arg_str = arg_pair.as_str();

    // Extract the bitwidth from the type of the argument
    let bitwidth = match ty {
        Type::BitVec(width) => *width,
        _ => {
            let msg = format!("Unsupported argument type: {:?}", ty);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        }
    };

    // Parse the argument value (first handle binary integers)
    if let Some(stripped) = arg_str
        .strip_prefix("0b")
        .or_else(|| arg_str.strip_prefix("0B"))
    {
        // Remove "0b" or "0B" prefix and underscores
        let binary_str = stripped.replace('_', "");
        if binary_str.is_empty() {
            let msg = format!("Empty binary integer: '{}'", arg_str);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        } else if !binary_str.chars().all(|c| c == '0' || c == '1') {
            // Ensure that all characters are binary digits
            let msg = format!(
                "Invalid binary integer '{}': contains non-binary digits",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        }
        let value = u64::from_str_radix(&binary_str, 2)
            .map_err(|e| format!("Invalid binary integer '{}': {}", arg_str, e))?;
        Ok(bv(value, bitwidth))
    } else if let Some(stripped) = arg_str
        .strip_prefix("0x")
        .or_else(|| arg_str.strip_prefix("0X"))
    {
        // Hex integers: remove "0x" or "0X" prefix and underscores
        let hex_str = stripped.replace('_', "");
        if hex_str.is_empty() {
            let msg = format!("Empty hexadecimal integer: '{}'", arg_str);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        } else if !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
            // Ensure that all characters are hex digits
            let msg = format!(
                "Invalid hexadecimal integer '{}': contains non-hex digits",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        }
        let value = u64::from_str_radix(&hex_str, 16)
            .map_err(|e| format!("Invalid hex integer '{}': {}", arg_str, e))?;
        // Each hex digit = 4 bits
        Ok(bv(value, bitwidth))
    } else {
        // Decimal integers: Remove underscores
        let decimal_str = arg_str.replace('_', "");
        if decimal_str.is_empty() {
            let msg = format!("Empty argument: '{}'", arg_str);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        } else if !decimal_str.chars().all(|c| c.is_ascii_digit()) {
            // Validate that all characters are decimal digits
            let msg = format!(
                "Invalid decimal integer '{}': contains non-digit characters",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(msg);
        }
        let value = decimal_str
            .parse::<u64>()
            .map_err(|e| format!("Invalid decimal integer '{}': {}", arg_str, e))?;
        Ok(bv(value, bitwidth))
    }
}
