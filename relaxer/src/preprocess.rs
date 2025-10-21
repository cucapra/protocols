use rustc_hash::FxHashMap;
use protocols::ir;

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
pub fn normalize_assignments(tr: &ir::Transaction, st: &ir::SymbolTable) -> ir::Transaction {
    // Create a new transaction with the same metadata
    let mut new_transaction = ir::Transaction::new(tr.name.clone());
    new_transaction.args = tr.args.clone();
    new_transaction.type_param = tr.type_param;

    // Get all DUT input pins
    let dut_struct = st[st
        .struct_id_from_name(
            st[tr
                .type_param
                .expect("Transaction must have a type parameter")]
            .name(),
        )
        .expect("Symbol Table must have struct in it")]
    .clone();

    let dut_input_pins: Vec<ir::SymbolId> = dut_struct
        .pins()
        .iter()
        .filter(|pin| pin.dir() == ir::Dir::In)
        .map(|pin| {
            st.symbol_id_from_name(&(dut_struct.name().to_owned() + "." + pin.name()))
                .expect("Struct pins and Symbol Table do not align")
                .clone()
        })
        .collect();

    // Initialize state: map each input pin to its current assignment StmtId (DontCare initially)
    let mut pin_state: FxHashMap<ir::SymbolId, ir::StmtId> = FxHashMap::default();
    for pin in &dut_input_pins {
        let dont_care_expr = new_transaction.expr_dont_care();
        let assign_stmt = new_transaction.s(ir::Stmt::Assign(*pin, dont_care_expr));
        pin_state.insert(*pin, assign_stmt);
    }

    // Get the body of the original transaction
    let body_stmt_id = tr.body;
    let body_stmts = match &tr[body_stmt_id] {
        ir::Stmt::Block(stmts) => stmts,
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
                ir::Stmt::Assign(symbol_id, _expr_id) => {
                    if dut_input_pins.contains(symbol_id) {
                        // Update pin state with this assignment StmtId (last assignment wins)
                        pin_state.insert(*symbol_id, stmt_id);
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
                let assign_stmt_id = pin_state[pin];
                new_body_stmts.push(assign_stmt_id);
            }

            // Move current_idx past this step
            current_idx = step_idx + 1;
        } else {
            // No more steps, we're done
            break;
        }
    }

    // Set the new body
    new_transaction.body = new_transaction.s(ir::Stmt::Block(new_body_stmts));

    new_transaction
}
