use std::collections::HashMap;

use log::{error, info};
use protocols::{
    ir::{Stmt, SymbolTable, Transaction},
    scheduler::Thread,
    serialize::serialize_args_mapping,
};

use crate::{
    designs::Design,
    signal_trace::{PortKey, SignalTrace, StepResult, WaveSignalTrace},
};

/// Queue of threads
type Queue<'a> = Vec<Thread<'a>>;

pub struct Scheduler<'a> {
    /// The current queue
    current_queue: Queue<'a>,
    /// The next queue
    next_queue: Queue<'a>,
}

impl<'a> Scheduler<'a> {
    /// Runs the `MiniInterpreter` on the Protocols file
    pub fn run(&mut self) {
        let mut current_stmt_id = self.transaction.body;
        loop {
            let stmt = &self.transaction[current_stmt_id];
            if let Stmt::Block(_) = stmt {
                info!("Beginning to evaluate statement block...")
            } else {
                info!(
                    "Evaluating statement `{}`",
                    self.format_stmt(&current_stmt_id)
                );
            }

            match self.evaluate_stmt(&current_stmt_id) {
                Ok(Some(next_stmt_id)) => {
                    info!(
                        "Next statement: {:?} `{}`",
                        next_stmt_id,
                        self.format_stmt(&next_stmt_id)
                    );

                    match self.transaction[next_stmt_id] {
                        Stmt::Fork => todo!("TODO: Figure out how to handle Fork"),
                        Stmt::Step => {
                            let step_result = self.trace.step();
                            info!("StepResult = {:?}", step_result);

                            // `trace.step()` returns a `StepResult` which is
                            // either `Done` or `Ok`.
                            // If `StepResult = Done`, there are no more steps
                            // left in the signal trace, so we set the
                            // `has_steps_remaining` flag to `false`
                            if let StepResult::Done = step_result {
                                self.has_steps_remaining = false;
                                info!("No steps remaining left in signal trace");

                                // The trace has ended, so we can just return here
                                self.has_errored = true;
                                break;
                            }
                            current_stmt_id = next_stmt_id;
                        }
                        _ => {
                            // Default "just keep going" case, in which we just
                            // proceed to the next `StmtId`
                            current_stmt_id = next_stmt_id;
                        }
                    }
                }

                // no more statements -> done
                Ok(None) => {
                    info!("Execution complete, no more statements.");
                    break;
                }

                // error -> record and stop
                Err(e) => {
                    error!("ERROR: {:?}, terminating thread", e);
                    self.has_errored = true;
                    break;
                }
            }
        }

        // If there were no errors, print the reconstructed transaction
        // (Note: we use `println!` instead of `info!` here so that we can see
        // what the transaction was without having to see all the other logs.)
        if !self.has_errored {
            println!("{}", self.serialize_reconstructed_transaction())
        }
    }
}
