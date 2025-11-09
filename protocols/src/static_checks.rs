use crate::{
    diagnostic::{DiagnosticHandler, Level},
    ir::{Dir, Expr, ExprId, SymbolId, SymbolTable, Transaction, Type},
    serialize::serialize_expr,
};
use anyhow::anyhow;
use itertools::Itertools;

/// Enum representing *language features* for which static well-formedness
/// checks need to be performed
pub enum LangFeature {
    /// Refers to `LHS := RHS`
    Assignments,
    /// Refers to `assert_eq`
    Assertions,
    /// Encompasses both if-statements and while-loops
    Conditionals,
}

/// Pretty-printer for `LangFeature` (used in error messages for reporting
/// well-formedness violations for these language features)
impl std::fmt::Display for LangFeature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LangFeature::Assignments => write!(f, "assignments"),
            LangFeature::Assertions => write!(f, "assert_eq"),
            LangFeature::Conditionals => write!(f, "conditions in if-statements / while-loops"),
        }
    }
}

/// Checks if the identifier corresponding to `symbol_id` is a DUT port /
/// function parameter with the specified `direction`.
/// - `expr_id` is the `ExprId` of the expression to which `symbol_id` belongs
///   (used for more accurate error message locations)
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
/// - `language_feature` is a `LangFeature` enum that describes the corresponding
///   language feature for which the well-formedness check is performed
///   (alsos used for error message purposes)
pub fn check_if_symbol_is_dut_port(
    symbol_id: SymbolId,
    direction: Dir,
    expr_id: ExprId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
    language_feature: LangFeature,
) -> anyhow::Result<()> {
    // Fully-qualify the name of the identifier
    let symbol_full_name = symbol_table.full_name_from_symbol_id(&symbol_id);

    match (tr.type_param, symbol_table[symbol_id].parent()) {
        (None, _) => {
            let error_msg = format!(
                "Expected {} to be an {}put parameter / {}put field of a struct, 
                            but the function {} is not parameterized by any structs",
                symbol_full_name, direction, direction, tr.name
            );
            handler.emit_diagnostic_expr(tr, &expr_id, &error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        (Some(_), None) => {
            // If we reach this case, then we know that
            // `symbol_id` is not a function parameter with the desired `direction`,
            // nor is it a field of a struct (since it has no parent)

            // Check if `symbol_id` is a parameter with the opposite direciton
            let has_opposite_direction = tr
                .get_parameters_by_direction(!direction)
                .contains(&symbol_id);

            let error_msg_prefix = if has_opposite_direction {
                format!(
                    "{} is an {}put parameter of {}, which is illegal 
                    (a {} parameter is expected in {})",
                    symbol_full_name, !direction, tr.name, direction, language_feature
                )
            } else {
                format!("Unrecognized identifier {}", symbol_full_name)
            };
            let error_msg = format!(
                            "{error_msg_prefix} 
                            (Only {}put parameters / {}put fields of structs are allowed to appear in {}",
                            direction,
                            direction,
                            language_feature
                        );
            handler.emit_diagnostic_expr(tr, &expr_id, &error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        (Some(struct_id), Some(parent_symbol_id)) => {
            // Check whether the name of the identifier corresponds
            // to a DUT port with the specified direction
            let struct_name = symbol_table[struct_id].name();
            if let Type::Struct(struct_id) = symbol_table[parent_symbol_id].tpe() {
                // `struct` is a reserved keyword in Rust,
                // so this variable of type `Struct`
                // is called `the_struct`
                let the_struct = &symbol_table[struct_id];

                // Fetch the names of all the DUT ports that have the desired
                // direction, qualified by the name of the struct *instance*
                let pins_with_desired_reiction = the_struct
                    .get_fields_by_direction(direction)
                    .map(|field| format!("{}.{}", struct_name, field))
                    .collect::<Vec<String>>();

                // If the identifier corresponds to a DUT port with the desired
                // direction, the check passes,
                // otherwise emit an error message
                if pins_with_desired_reiction.contains(&symbol_full_name) {
                    Ok(())
                } else {
                    let error_msg = format!(
                        "`{}` is not an {}put field of the struct `{}` (Only {}put fields are allowed to appear in {})",
                        symbol_full_name, direction, struct_name, direction, language_feature
                    );
                    handler.emit_diagnostic_expr(tr, &expr_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            } else {
                let parent_name = symbol_table[parent_symbol_id].name();
                let error_msg = format!(
                    "Expected {} to be an output field of struct {}({}) but got {}({}) as the parent instead",
                    serialize_expr(tr, symbol_table, &expr_id),
                    struct_name,
                    struct_id,
                    parent_name,
                    parent_symbol_id
                );
                handler.emit_diagnostic_expr(tr, &expr_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
    }
}

/// Checks whether the condition (guard) for an if-statement / while-loop
/// conforms to the well-formedness requirements
pub fn check_condition_well_formedness(
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
    expr_id: &ExprId,
) -> anyhow::Result<()> {
    let expr = &tr[expr_id];
    match expr {
        Expr::Const(_) => Ok(()),
        Expr::Sym(symbol_id) => {
            // Check if the identifier is a DUT output port or an output parameter
            let is_output_param = tr.get_parameters_by_direction(Dir::Out).contains(symbol_id);
            if is_output_param {
                Ok(())
            } else {
                check_if_symbol_is_dut_port(
                    *symbol_id,
                    Dir::Out,
                    *expr_id,
                    tr,
                    symbol_table,
                    handler,
                    LangFeature::Conditionals,
                )
            }
        }
        Expr::DontCare => {
            let error_msg =
                "DontCare not allowed inside conditions for if-statements & while-loops";
            handler.emit_diagnostic_expr(tr, expr_id, error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        Expr::Binary(_, expr_id1, expr_id2) => {
            check_condition_well_formedness(tr, symbol_table, handler, expr_id1)?;
            check_condition_well_formedness(tr, symbol_table, handler, expr_id2)
        }
        Expr::Unary(_, inner_expr) => {
            check_condition_well_formedness(tr, symbol_table, handler, inner_expr)
        }
        Expr::Slice(sliced_expr, _, _) => {
            check_condition_well_formedness(tr, symbol_table, handler, sliced_expr)
        }
    }
}

// TODO: complete this function
#[allow(dead_code, unused_variables)]
pub fn check_assertion_well_formedness(
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
    expr_id: &ExprId,
) -> anyhow::Result<()> {
    todo!()
}

// TODO: refactor the logic for checking assignment WF-ness from `monitor/src/interpreter.rs`
// into a helper function `check_assignment_well_formedness`
