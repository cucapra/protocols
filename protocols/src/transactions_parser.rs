use crate::ir::Type;
use crate::scheduler::TodoItem;
use crate::{diagnostic::*, setup::bv};
use anyhow::anyhow;
use baa::BitVecValue;
use pest::{error::InputLocation, iterators::Pair, Parser};
use pest_derive::Parser;
use rustc_hash::FxHashMap;

#[derive(Parser)]
#[grammar = "transactions.pest"]
struct TransactionsParser;

/// Parses a transaction file (specified at `filepath`) using a particular `DiagnosticHandler`.
/// The argument `transaction_arg_types` maps a transaction's name to its argument types.
pub fn parse_transactions_file(
    filepath: impl AsRef<std::path::Path>,
    handler: &mut DiagnosticHandler,
    transaction_arg_types: FxHashMap<String, Vec<Type>>,
) -> anyhow::Result<Vec<TodoItem>> {
    let filename = filepath.as_ref().to_str().unwrap().to_string();
    let input = std::fs::read_to_string(filepath).map_err(|e| anyhow!("failed to load: {}", e))?;
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
        return Err(anyhow!(msg));
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
                .unwrap_or_else(|| {
                    panic!("Unable to fetch argument types for transaction {function_name}")
                });

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
) -> anyhow::Result<Vec<BitVecValue>> {
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
        return Err(anyhow!(msg));
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

/// Datatype that defines the format of integer literals accepted by the
/// parser for transactions file (either decimal, binary or hex)
#[derive(Debug)]
enum IntFormat {
    Decimal,
    Binary,
    Hex,
}

impl IntFormat {
    /// Converts an integer format to its radix
    /// (i.e. `Hex` is 16, `Binary` is 2, etc.)
    fn radix(&self) -> u32 {
        match self {
            IntFormat::Decimal => 10,
            IntFormat::Binary => 2,
            IntFormat::Hex => 16,
        }
    }

    /// Parses a string into a `BitVecValue` based on the specified `bitwidth`
    /// and `IntFormat`
    fn parse_bitvec_value(&self, arg_str: String, bitwidth: u32) -> BitVecValue {
        let error_msg = match self {
            IntFormat::Decimal => "Invalid decimal integer",
            IntFormat::Binary => "Invalid binary integer",
            IntFormat::Hex => "Invalid hex integer",
        };

        if bitwidth <= 64 {
            // If bitwidth <= 64, try to parse it as a u64
            let value = u64::from_str_radix(&arg_str, self.radix())
                .unwrap_or_else(|e| panic!("{} '{}': {}", error_msg, arg_str, e));
            bv(value, bitwidth)
        } else {
            // Otherwise, try to parse it as a u128
            u128::from_str_radix(&arg_str, self.radix())
                .map(|v| BitVecValue::from_u128(v, 128))
                .unwrap_or_else(|e| panic!("{} '{}': {}", error_msg, arg_str, e))
        }
    }
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
) -> anyhow::Result<BitVecValue> {
    let arg_str = arg_pair.as_str();

    // Extract the bitwidth from the type of the argument
    let bitwidth = match ty {
        Type::BitVec(width) => *width,
        _ => {
            let msg = format!("Unsupported argument type: {:?}", ty);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
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
            return Err(anyhow!(msg));
        } else if !binary_str.chars().all(|c| c == '0' || c == '1') {
            // Ensure that all characters are binary digits
            let msg = format!(
                "Invalid binary integer '{}': contains non-binary digits",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
        }
        Ok(IntFormat::Binary.parse_bitvec_value(binary_str, bitwidth))
    } else if let Some(stripped) = arg_str
        .strip_prefix("0x")
        .or_else(|| arg_str.strip_prefix("0X"))
    {
        // Hex integers: remove "0x" or "0X" prefix and underscores
        let hex_str = stripped.replace('_', "");
        if hex_str.is_empty() {
            let msg = format!("Empty hexadecimal integer: '{}'", arg_str);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
        } else if !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
            // Ensure that all characters are hex digits
            let msg = format!(
                "Invalid hexadecimal integer '{}': contains non-hex digits",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
        }

        Ok(IntFormat::Hex.parse_bitvec_value(hex_str, bitwidth))
    } else {
        // Decimal integers: Remove underscores
        let decimal_str = arg_str.replace('_', "");
        if decimal_str.is_empty() {
            let msg = format!("Empty argument: '{}'", arg_str);
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
        } else if !decimal_str.chars().all(|c| c.is_ascii_digit()) {
            // Validate that all characters are decimal digits
            let msg = format!(
                "Invalid decimal integer '{}': contains non-digit characters",
                arg_str
            );
            handler.emit_diagnostic_parsing(&msg, fileid, arg_pair, Level::Error);
            return Err(anyhow!(msg));
        }
        Ok(IntFormat::Decimal.parse_bitvec_value(decimal_str, bitwidth))
    }
}
