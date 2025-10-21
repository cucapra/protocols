use protocols::ir;
use rustc_hash::FxHashMap;

/// Compiler pass that normalizes a transaction to have assignments for all DUT input pins
/// immediately after each step() call. If if an assignment to a DUT input is reassigned,
/// the last assignment before the step() takes precedence.
///
/// Precondition: The transaction must not contain any control flow (while, if/else).
///
/// Algorithm:
/// 1. Get all DUT input pins from the type parameter
/// 2. Iterate through the transaction body (straight-line code)
/// 3. Track the most recent assignment to each input pin
/// 4. At each step():
///    - Collect all current assignments
///    - Remove assignment statements from the body
///    - Insert assignments for ALL input pins right after the step
pub fn normalize_assignments(tr: &mut ir::Transaction, st: &ir::SymbolTable) {
    // Get all DUT input pins
    let dut_struct = match st[tr
        .type_param
        .expect("Transaction must have a type parameter")]
    .tpe()
    {
        ir::Type::Struct(struct_id) => &st[struct_id],
        _ => panic!("Transaction type parameter must be a struct"),
    };

    let dut_input_pins: Vec<ir::SymbolId> = dut_struct
        .pins()
        .iter()
        .filter(|pin| pin.dir() == ir::Dir::In)
        .map(|pin| {
            st.symbol_id_from_name(
                &(st[tr.type_param.expect("")].name().to_owned() + "." + pin.name()),
            )
            .expect("Struct pins and Symbol Table do not align")
            .clone()
        })
        .collect();

    // Initialize state: map each input pin to its current assignment ExprId (DontCare initially)
    let mut pin_state: FxHashMap<ir::SymbolId, ir::ExprId> = FxHashMap::default();
    for pin in &dut_input_pins {
        let dont_care_expr = tr.expr_dont_care();
        pin_state.insert(*pin, dont_care_expr);
    }

    // Get the body of the original transaction (clone to avoid borrow issues)
    let body_stmt_id = tr.body;
    let body_stmts = match &tr[body_stmt_id] {
        ir::Stmt::Block(stmts) => stmts.clone(),
        _ => panic!("Transaction body must be a Block"),
    };

    // Process the body and build new statement list
    let mut new_body_stmts: Vec<ir::StmtId> = Vec::new();
    let mut current_idx = 0;

    // Iterate through segments between steps
    while current_idx < body_stmts.len() {
        // Scan forward from current position until we hit a step or end of body
        let mut next_step_idx: Option<usize> = None;

        // Look for the next step starting from current_idx
        for i in current_idx..body_stmts.len() {
            if matches!(tr[body_stmts[i]], ir::Stmt::Step) {
                next_step_idx = Some(i);
                break;
            }
        }

        // Process all statements in this segment (from current_idx to next step or end)
        let segment_end = next_step_idx.unwrap_or(body_stmts.len());

        for i in current_idx..segment_end {
            let stmt_id = body_stmts[i];
            match &tr[stmt_id] {
                ir::Stmt::Assign(symbol_id, expr_id) => {
                    if dut_input_pins.contains(symbol_id) {
                        // Update pin state with this assignment ExprId (last assignment wins)
                        pin_state.insert(*symbol_id, *expr_id);
                        // Don't add to new_body_stmts - we'll insert after the step
                    } else {
                        // Non-input assignment, keep it in place
                        new_body_stmts.push(stmt_id);
                    }
                }
                ir::Stmt::Fork => {
                    // Keep fork statement
                    new_body_stmts.push(stmt_id);
                }
                ir::Stmt::AssertEq(_, _) => {
                    // Keep assert_eq statement
                    new_body_stmts.push(stmt_id);
                }
                ir::Stmt::While(_, _) | ir::Stmt::IfElse(_, _, _) => {
                    panic!("Precondition violated: transaction contains control flow");
                }
                ir::Stmt::Block(_) => {
                    panic!("Nested blocks not expected in straight-line code");
                }
                ir::Stmt::Step => {
                    // Should not happen in this loop since we stop before steps
                    unreachable!();
                }
            }
        }

        // If we found a step, insert it and then insert all pin assignments
        if let Some(step_idx) = next_step_idx {
            // Insert the step statement
            new_body_stmts.push(body_stmts[step_idx]);

            // Insert assignments for all DUT input pins right after this step
            for pin in &dut_input_pins {
                let expr_id = pin_state[pin];
                let assign_stmt = tr.s(ir::Stmt::Assign(*pin, expr_id));
                new_body_stmts.push(assign_stmt);
            }

            // Move current_idx past this step
            current_idx = step_idx + 1;
        } else {
            // No more steps, we're done
            break;
        }
    }

    // Set the new body
    tr.body = tr.s(ir::Stmt::Block(new_body_stmts));
}

#[cfg(test)]
pub mod tests {
    use baa::BitVecValue;
    use insta::Settings;
    use std::path::Path;
    use strip_ansi_escapes::strip_str;

    use super::*;
    use crate::diagnostic::DiagnosticHandler;
    use crate::parser::parse_file;
    use crate::serialize::serialize_to_string;

    fn snap(name: &str, content: String) {
        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(name, content);
        });
    }

    // fn test_helper(filename: &str, snap_name: &str) {
    //     let mut handler = DiagnosticHandler::default();
    //     let result = parse_file(filename, &mut handler);

    //     let content = match result {
    //         Ok(trs) => serialize_to_string(trs).unwrap(),
    //         Err(_) => strip_str(handler.error_string()),
    //     };
    //     println!("{}", content);
    //     // snap(snap_name, content);
    // }

    fn test_helper(filename: &str, _snap_name: &str) {
        let mut handler = DiagnosticHandler::default();
        let result = parse_file(filename, &mut handler);
        let mut new_trs: Vec<(ir::SymbolTable, ir::Transaction)> = Vec::new();

        // create a new vector of (st, tr) pairs by running
        // the normalize_assignments pass on every transaction
        // then serialize the result (or produce the error string).
        let content = match result {
            Ok(trs) => {
                // Consume the parsed vector of (SymbolTable, Transaction) pairs,
                // normalize each transaction with its corresponding symbol table,
                // and collect the results for serialization.
                println!("OK!");
                for (st, mut tr) in trs.into_iter() {
                    normalize_assignments(&mut tr, &st);
                    // println!("==== Normalized Transaction ====");
                    // println!("{:?}", tr);
                    new_trs.push((st, tr));
                }
                serialize_to_string(new_trs).unwrap()
            }
            Err(_) => "failed".to_string(),
        };
        // println!("==== Normalized Transaction ====");

        println!("{}", content);
        // snap("add_d1", content);
    }

    #[test]
    fn test_add_transaction() {
        test_helper("tests/adders/add_d1.prot", "add_d1");
    }
}
