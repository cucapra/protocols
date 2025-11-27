// Copyright 2025 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use crate::{
    diagnostic::{DiagnosticHandler, Level},
    ir::{BinOp, Dir, Expr, ExprId, LocationId, StmtId, SymbolId, SymbolTable, Transaction, Type},
    serialize::serialize_expr,
};
use anyhow::anyhow;

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
/// - `location_id` is the `LocationId` (either an `ExprId` or a `StmtId`)
///   to which `symbol_id` belongs
///   (this is used for more accurate error message locations)
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
/// - `language_feature` is a `LangFeature` enum that describes the corresponding
///   language feature for which the well-formedness check is performed
///   (also used for error message purposes)
pub fn check_if_symbol_is_dut_port(
    symbol_id: SymbolId,
    direction: Dir,
    location_id: LocationId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
    lang_feature: LangFeature,
) -> anyhow::Result<()> {
    // Fully-qualify the name of the identifier
    let symbol_full_name = symbol_table.full_name_from_symbol_id(&symbol_id);

    match (tr.type_param, symbol_table[symbol_id].parent()) {
        (None, _) => {
            let error_msg = format!(
                "Expected {} to be a struct's {}put field,
                but the function {} is not parameterized by any structs",
                symbol_full_name, direction, tr.name
            );
            handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        (Some(_), None) => {
            // The identifier doesn't have a parent, so we need to
            // perform more granular analysis before emitting the error message
            match lang_feature {
                // Function parameters are not allowed to appear in assignments
                LangFeature::Assignments => {
                    let error_msg = format!(
                        "Cannot assign to function argument {}. Try using assert_eq if you want to check the value of a transaction output.",
                        symbol_full_name
                    );
                    handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
                LangFeature::Assertions => {
                    // Only output parameters are allowed in assertions
                    let is_output_param = tr.is_param_with_direction(symbol_id, Dir::Out);
                    if is_output_param {
                        Ok(())
                    } else {
                        // Output parameters to functions are forbidden in assertions
                        let error_msg = format!(
                            "`{}` is an input parameter of the function `{}`, but `{}` cannot mention input parameters",
                            symbol_full_name, tr.name, lang_feature
                        );
                        handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
                        Err(anyhow!(error_msg))
                    }
                }
                LangFeature::Conditionals => {
                    // Input/output parameters of functions are not allowed
                    // to appear in conditions
                    let error_msg = format!(
                        "{} is a function argument, but {} cannot mention function arguments",
                        symbol_full_name, lang_feature
                    );
                    handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            }
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
                let pins_with_desired_direction = the_struct
                    .get_fields_by_direction(direction)
                    .map(|field| format!("{}.{}", struct_name, field))
                    .collect::<Vec<String>>();

                // If the identifier corresponds to a DUT port with the desired
                // direction, the check passes,
                // otherwise emit an error message
                if pins_with_desired_direction.contains(&symbol_full_name) {
                    Ok(())
                } else {
                    let error_msg = format!(
                        "`{}` is a {}put field of the struct `{}`, but only {}put fields are allowed to appear in {})",
                        symbol_full_name, !direction, struct_name, direction, lang_feature
                    );
                    handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                }
            } else {
                let parent_name = symbol_table[parent_symbol_id].name();
                let error_msg = format!(
                    "Expected {} to be an output field of struct {}({}) but got {}({}) as the parent struct instead",
                    symbol_full_name, struct_name, struct_id, parent_name, parent_symbol_id
                );
                handler.emit_diagnostic(tr, &location_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
    }
}

/// Helper function to check if a symbol is a DUT port with any direction (input or output)
/// without emitting diagnostics. Returns true if it's a port (input or output), false otherwise.
fn is_dut_port(
    symbol_id: SymbolId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
) -> bool {
    // Check if this is a struct field
    if let (Some(struct_id), Some(parent_symbol_id)) = (tr.type_param, symbol_table[symbol_id].parent()) {
        if let Type::Struct(_) = symbol_table[parent_symbol_id].tpe() {
            return true;
        }
    }
    false
}

/// Checks whether the condition (guard) for an if-statement / while-loop
/// conforms to the well-formedness (WF) requirements.
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
pub fn check_condition_wf(
    expr_id: &ExprId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    let expr = &tr[expr_id];
    match expr {
        Expr::Const(_) => Ok(()),
        Expr::Sym(symbol_id) => {
            // Allow both input and output parameters/ports in conditions
            // Check if it's a function parameter (input or output)
            if tr.is_param_with_direction(*symbol_id, Dir::Out)
                || tr.is_param_with_direction(*symbol_id, Dir::In) {
                Ok(())
            } else if is_dut_port(*symbol_id, tr, symbol_table) {
                // It's a DUT port (input or output), which is allowed
                Ok(())
            } else {
                // Not a parameter or DUT port, emit error
                let symbol_full_name = symbol_table.full_name_from_symbol_id(symbol_id);
                let error_msg = format!(
                    "{} is a function argument, but {} cannot mention function arguments",
                    symbol_full_name, LangFeature::Conditionals
                );
                handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                Err(anyhow!(error_msg))
            }
        }
        Expr::DontCare => {
            let error_msg =
                "DontCare not allowed inside conditions for if-statements & while-loops";
            handler.emit_diagnostic_expr(tr, expr_id, error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        Expr::Binary(_, expr_id1, expr_id2) => {
            check_condition_wf(expr_id1, tr, symbol_table, handler)?;
            check_condition_wf(expr_id2, tr, symbol_table, handler)
        }
        Expr::Unary(_, inner_expr) | Expr::Slice(inner_expr, _, _) => {
            check_condition_wf(inner_expr, tr, symbol_table, handler)
        }
    }
}

/// Checks whether an argument of an assertion (identified by its `ExprId`)
/// is well-formed (WF).
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
pub fn check_assertion_arg_wf(
    expr_id: &ExprId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    let expr = &tr[expr_id];
    match expr {
        Expr::Const(_) => Ok(()),
        Expr::Sym(symbol_id) => {
            // Check if the identifier is an output parameter of the function
            if tr.is_param_with_direction(*symbol_id, Dir::Out) {
                Ok(())
            } else {
                // Check if the identifier is a DUT output port
                check_if_symbol_is_dut_port(
                    *symbol_id,
                    Dir::Out,
                    LocationId::Expr(*expr_id),
                    tr,
                    symbol_table,
                    handler,
                    LangFeature::Assertions,
                )
            }
        }
        Expr::DontCare => {
            let error_msg = "DontCare expressions not allowed inside assert_eq";
            handler.emit_diagnostic_expr(tr, expr_id, error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        Expr::Binary(_, expr_id1, expr_id2) => {
            check_assertion_arg_wf(expr_id1, tr, symbol_table, handler)?;
            check_assertion_arg_wf(expr_id2, tr, symbol_table, handler)
        }
        Expr::Unary(_, inner_expr) => check_assertion_arg_wf(inner_expr, tr, symbol_table, handler),
        Expr::Slice(sliced_expr, _, _) => {
            check_assertion_arg_wf(sliced_expr, tr, symbol_table, handler)
        }
    }
}

/// Checks whether an assertion (an `assert_eq` statement) is well-formed (WF).
/// -`expr_id1` & `expr_id2` are the `ExprId` of the two arguments supplied to
///   `assert_eq`.
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
pub fn check_assertion_wf(
    expr_id1: &ExprId,
    expr_id2: &ExprId,
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    // Check assertion well-formedness twice, once with `expr_id1` as the LHS
    // & `expr_id2` as the RHS, and once with the LHS/RHS swapped
    // (We need to do this since there is no way a priori to determine which
    // argument is the LHS/RHS, as `assert_eq` is symmetric in its arguments)

    check_assertion_arg_wf(expr_id1, tr, st, handler)?;
    check_assertion_arg_wf(expr_id2, tr, st, handler)
}

/// Recursively checks whether the RHS of an assignment
/// (identified by `rhs_expr_id`) is well-formed (WF).
/// - The `dont_cares_allowed` argument is used to determine whether
///   `DontCare` is allowed to appear during the particular call to this function.
///   This arg is set to `true` in the top-level call to this function since we
///   allow `DontCare` to appear as the only expression on the RHS of an
///   assignment, but we set to `false` during recursive calls since we don't
///   allow `DontCare` to appear as an argument to unary/binary/slice operators.
pub fn check_assignment_rhs_wf(
    rhs_expr_id: &ExprId,
    dont_cares_allowed: bool,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    let rhs_expr = &tr[rhs_expr_id];
    match rhs_expr {
        Expr::Const(_) => Ok(()),
        Expr::DontCare if dont_cares_allowed => Ok(()),
        Expr::DontCare => {
            // We need this case to prevent DontCares from appearing as a sub-expression on the RHS
            // (DontCare is only allowed as the *only* expression on the RHS of an assignment)
            let error_msg = "DontCare cannot appear as a sub-expression on the RHS of an assignment. 
                        If you need a DontCare on the RHS of assignment, 
                        change the statement to `<lhs> := X` where `DontCare` is the *only* expression on the RHS.";
            handler.emit_diagnostic_expr(tr, rhs_expr_id, error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        Expr::Sym(symbol_id) => {
            // The only kind of identifier which is allowed on
            // the RHS of an assignment is an input parameter
            // All other kinds of identifiers are forbidden
            if tr.is_param_with_direction(*symbol_id, Dir::In) {
                Ok(())
            } else {
                // Output parameters are not allowed to appear on the RHS of assignments
                if tr.is_param_with_direction(*symbol_id, Dir::Out) {
                    let error_msg = format!(
                        "`{}` is an output parameter of the function `{}`, but output parameters are not allowed to appear on the RHS of assignments",
                        serialize_expr(tr, symbol_table, rhs_expr_id),
                        tr.name
                    );
                    handler.emit_diagnostic_expr(tr, rhs_expr_id, &error_msg, Level::Error);
                    Err(anyhow!(error_msg))
                } else {
                    // Only output fields of structs are allowed to appear on the RHS of assignments
                    if symbol_table[symbol_id].parent().is_some() {
                        check_if_symbol_is_dut_port(
                            *symbol_id,
                            Dir::Out,
                            LocationId::Expr(*rhs_expr_id),
                            tr,
                            symbol_table,
                            handler,
                            LangFeature::Assignments,
                        )
                    } else {
                        // Generic error message for invalid identifiers
                        // (e.g. the user referred to a non-existent variable)
                        let error_msg = format!(
                            "Invalid identifier {} on the RHS of an assignment",
                            symbol_table[symbol_id].name()
                        );
                        handler.emit_diagnostic_expr(tr, rhs_expr_id, &error_msg, Level::Error);
                        Err(anyhow!(error_msg))
                    }
                }
            }
        }
        Expr::Binary(BinOp::Concat, expr_id1, expr_id2) => {
            // Recursively check whether the two operands are well-formed
            // (Note that we disallow `DontCare`s to appear as arguments
            // to the concatenation)
            check_assignment_rhs_wf(expr_id1, false, tr, symbol_table, handler)?;
            check_assignment_rhs_wf(expr_id2, false, tr, symbol_table, handler)
        }
        Expr::Binary(_, _, _) => {
            // Other binary operators (e.g. the `==` comparison operator)
            // are not allowed on the RHS of assignments
            let error_msg = format!(
                "Unsupported binary operation {} on the RHS of an assignment",
                serialize_expr(tr, symbol_table, rhs_expr_id)
            );
            handler.emit_diagnostic_expr(tr, rhs_expr_id, &error_msg, Level::Error);
            Err(anyhow!(error_msg))
        }
        Expr::Unary(_, inner_expr) | Expr::Slice(inner_expr, _, _) => {
            // Check if the inner expression is well-formed
            // (Note: we do not allow the inner expression to be `DontCare`)
            check_assignment_rhs_wf(inner_expr, false, tr, symbol_table, handler)
        }
    }
}

/// Checks whether an assignment is well-formed.
/// - `lhs_symbol_id` & `rhs_expr_id` correspond to the LHS & RHS of the
///   assignment respectively
/// - `stmt_id` is the `StmtId` of the entire assignemnt statemnet
///   (used to track the location of the statement in error messages)
/// - The associated `Transaction`, `SymbolTable` & `DiagnosticHandler`
///   are also expected as inputs (for error message purposes)
pub fn check_assignment_wf(
    lhs_symbol_id: &SymbolId,
    rhs_expr_id: &ExprId,
    stmt_id: &StmtId,
    tr: &Transaction,
    symbol_table: &SymbolTable,
    handler: &mut DiagnosticHandler,
) -> anyhow::Result<()> {
    // Check if the LHS is a DUT input port
    check_if_symbol_is_dut_port(
        *lhs_symbol_id,
        Dir::In,
        LocationId::Stmt(*stmt_id),
        tr,
        symbol_table,
        handler,
        LangFeature::Assignments,
    )?;

    // Check if the RHS is well-formed
    check_assignment_rhs_wf(rhs_expr_id, true, tr, symbol_table, handler)
}
