use crate::{
    diagnostic::{DiagnosticHandler, Level},
    ir::{Expr, ExprId, SymbolTable, Transaction, Type},
    serialize::serialize_expr,
};
use anyhow::anyhow;
use itertools::Itertools;

/// Checks whether the condition (guard) for an if-statement / while-loop
/// conforms to the well-formedness requirements
pub fn check_condition_well_formedness(
    tr: &Transaction,
    st: &SymbolTable,
    handler: &mut DiagnosticHandler,
    expr_id: &ExprId,
) -> anyhow::Result<()> {
    let expr = &tr[expr_id];
    match expr {
        Expr::Const(_) => Ok(()),
        Expr::Sym(symbol_id) => {
            // Check if the identifier is a DUT output port or an output parameter
            let is_output_param = tr.get_output_param_symbols().contains(symbol_id);
            if is_output_param {
                Ok(())
            } else {
                match (tr.type_param, st[symbol_id].parent()) {
                    (None, None) => todo!(),
                    (None, Some(_)) | (Some(_), None) => todo!(),
                    (Some(struct_id), Some(parent_symbol_id)) => {
                        // Check whether the name of the identifier corresponds
                        // to a DUT output port
                        let struct_name = st[struct_id].name();
                        if let Type::Struct(struct_id) = st[parent_symbol_id].tpe() {
                            let the_struct = &st[struct_id];
                            // Fetch the (qualified) names of all the output pins and check
                            // if `symbol_full_name` is one of them
                            let mut output_pin_names = the_struct.get_output_pin_names();
                            let symbol_full_name = st.full_name_from_symbol_id(symbol_id);
                            if output_pin_names.contains(&symbol_full_name) {
                                Ok(())
                            } else {
                                println!(
                                    "output fields: {:?}",
                                    output_pin_names.collect::<Vec<_>>()
                                );
                                let error_msg = format!(
                                    "{} is not an output field of struct {} but only output fields of {} are allowed to appear in the condition for loops/if-statements",
                                    symbol_full_name, struct_name, struct_name
                                );
                                handler.emit_diagnostic_expr(tr, expr_id, &error_msg, Level::Error);
                                Err(anyhow!(error_msg))
                            }
                        } else {
                            let parent_name = st[parent_symbol_id].name();
                            let error_msg = format!(
                                "Expected {} to be an output field of struct {}({}) but got {}({}) as the parent instead",
                                serialize_expr(tr, st, expr_id),
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
            check_condition_well_formedness(tr, st, handler, expr_id1)?;
            check_condition_well_formedness(tr, st, handler, expr_id2)
        }
        Expr::Unary(_, inner_expr) => check_condition_well_formedness(tr, st, handler, inner_expr),
        Expr::Slice(sliced_expr, _, _) => {
            check_condition_well_formedness(tr, st, handler, sliced_expr)
        }
    }
}
