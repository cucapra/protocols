use crate::{
    diagnostic::{DiagnosticHandler, Level},
    ir::{Dir, Expr, ExprId, SymbolTable, Transaction, Type},
    serialize::serialize_expr,
};
use anyhow::anyhow;
use itertools::Itertools;

// pub fn is_dut_port(symbol_id: SymbolId, tr: &Transaction) -> bool {}

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
                // Fully-qualify the name of the identifier
                let symbol_full_name = symbol_table.full_name_from_symbol_id(symbol_id);

                match (tr.type_param, symbol_table[symbol_id].parent()) {
                    (None, _) => {
                        let error_msg = format!(
                            "Expected {} to be an output parameter or an output field of a struct, 
                            but the function {} is not parameterized by any structs",
                            symbol_full_name, tr.name
                        );
                        handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                        Err(anyhow!(error_msg))
                    }
                    (Some(_), None) => {
                        // If we reach this case, then we know that
                        // `symbol_id` is neither an output parameter nor
                        // is it a field of a struct (since it has no parent),
                        // in which case, it must be an input parameter
                        let is_input_param =
                            tr.get_parameters_by_direction(Dir::In).contains(symbol_id);

                        let error_msg_prefix = if is_input_param {
                            format!(
                                "{} is an input parameter of {}, which is illegal",
                                symbol_full_name, tr.name
                            )
                        } else {
                            format!("Unrecognized identifier {}", symbol_full_name)
                        };
                        let error_msg = format!(
                            "{error_msg_prefix} (Only output parameters / output fields of structs are allowed to appear in the conditions for if-statements / while-loops)"
                        );
                        handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                        Err(anyhow!(error_msg))
                    }
                    (Some(struct_id), Some(parent_symbol_id)) => {
                        // Check whether the name of the identifier corresponds
                        // to a DUT output port
                        let struct_name = symbol_table[struct_id].name();
                        if let Type::Struct(struct_id) = symbol_table[parent_symbol_id].tpe() {
                            // `struct` is a reserved keyword in Rust,
                            // so this variable of type `Struct`
                            // is called `the_struct`
                            let the_struct = &symbol_table[struct_id];

                            // Fetch the names of all the output pins,
                            // qualified by the name of the struct *instance*
                            let output_pin_names = the_struct
                                .get_fields_by_direction(Dir::Out)
                                .map(|field| format!("{}.{}", struct_name, field))
                                .collect::<Vec<String>>();

                            // If the identifier corresponds to a DUT output port,
                            // the condition is well-formed, otherwise
                            // emit an error message
                            if output_pin_names.contains(&symbol_full_name) {
                                Ok(())
                            } else {
                                let error_msg = format!(
                                    "`{}` is not an output field of the struct `{}` 
                                    (Only output fields are allowed to appear in conditions for loops/if-statements",
                                    symbol_full_name, struct_name
                                );
                                handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                                Err(anyhow!(error_msg))
                            }
                        } else {
                            let parent_name = symbol_table[parent_symbol_id].name();
                            let error_msg = format!(
                                "Expected {} to be an output field of struct {}({}) but got {}({}) as the parent instead",
                                serialize_expr(tr, symbol_table, expr_id),
                                struct_name,
                                struct_id,
                                parent_name,
                                parent_symbol_id
                            );
                            handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                            Err(anyhow!(error_msg))
                        }
                    }
                }
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

// TODO: refactor the logic for checking assignment WF-ness from `monitor/src/interpreter.rs`
// into a helper function `check_assignment_well_formedness`

// TODO: implement a helper function that checks well-formedness of assertions
