use crate::scheduler::TodoItem;
use crate::{diagnostic::*, setup::bv};
use baa::BitVecValue;
use pest::{Parser, error::InputLocation, iterators::Pair};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "transactions.pest"]
struct TransactionsParser;

/// Parses a transaction file (specified at `filepath`) using a particular `DiagnosticHandler`
pub fn parse_transactions_file(
    filepath: impl AsRef<std::path::Path>,
    handler: &mut DiagnosticHandler,
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

            // Parse arguments if they exist
            let mut args = vec![];
            if let Some(arglist_pair) = transaction_inner.next() {
                if arglist_pair.as_rule() == Rule::arglist {
                    args = parse_arglist(arglist_pair, handler, fileid)?;
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
fn parse_arglist(
    arglist_pair: Pair<Rule>,
    handler: &mut DiagnosticHandler,
    fileid: usize,
) -> Result<Vec<BitVecValue>, String> {
    let mut args = vec![];

    for inner_pair in arglist_pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::arg => {
                let arg_value = parse_arg(inner_pair, handler, fileid)?;
                args.push(arg_value);
            }
            Rule::arglist => {
                // Recursively parse nested arglist
                let mut nested_args = parse_arglist(inner_pair, handler, fileid)?;
                args.append(&mut nested_args);
            }
            _ => {
                // Skip other rules like commas
                continue;
            }
        }
    }

    Ok(args)
}

/// Parses one single argument to a transaction, returning a `BitVecValue`
/// Arguments:
/// - `arg_pair` is a `Pair` produced by the parser derived by Pest
/// - `handler` is the handler for emitting error diagnostics
/// - `fileid`: file descriptor
fn parse_arg(
    arg_pair: Pair<Rule>,
    _handler: &mut DiagnosticHandler,
    _fileid: usize,
) -> Result<BitVecValue, String> {
    let arg_str = arg_pair.as_str();

    // TODO: figure out how to avoid hard-coding the `bitwidth`
    let bitwidth = 32;

    if arg_str.starts_with("0b") || arg_str.starts_with("0B") {
        // Remove "0b" or "0B" prefix and underscores
        let binary_str = arg_str[2..].replace('_', "");
        let value = u64::from_str_radix(&binary_str, 2)
            .map_err(|e| format!("Invalid binary integer '{}': {}", arg_str, e))?;
        Ok(bv(value, bitwidth))
    } else if arg_str.starts_with("0x") || arg_str.starts_with("0X") {
        // Remove "0x" or "0X" prefix and underscores
        let hex_str = arg_str[2..].replace('_', "");
        let value = u64::from_str_radix(&hex_str, 16)
            .map_err(|e| format!("Invalid hex integer '{}': {}", arg_str, e))?;
        // Each hex digit = 4 bits
        Ok(bv(value, bitwidth))
    } else {
        // Everything else is treated as a decimal integer
        // Remove underscores
        let decimal_str = arg_str.replace('_', "");
        let value = decimal_str
            .parse::<u64>()
            .map_err(|e| format!("Invalid decimal integer '{}': {}", arg_str, e))?;
        Ok(bv(value, bitwidth))
    }
}
