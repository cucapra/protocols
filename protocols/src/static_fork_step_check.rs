use crate::diagnostic::{DiagnosticHandler, Level};
use crate::ir::*;

/// Conservative static analysis for our step and fork rules:
/// 1. fork must come after a step
/// 2. any execution of a protocol must fork exactly 0 or 1 time
/// 3. protocols must end in a step
/// 4. a loop must contain at least one step, otherwise the protocol can never terminate
pub fn check_step_and_fork(
    protocols: &Vec<(Transaction, SymbolTable)>,
    diag: &mut DiagnosticHandler,
) -> u32 {
    let mut error_count = 0;
    for (proto, _) in protocols {
        let final_stmts =
            analyze_stmt(diag, &mut error_count, proto, proto.body, State::default()).final_stmts;
        match final_stmts.as_slice() {
            [one] if !is_step(proto, *one) => {
                let msg = format!("Final statement in `{}` is not a step.", proto.name);
                diag.emit_diagnostic_stmt(proto, one, &msg, Level::Error);
                error_count += 1;
            }
            _ => {} // if there are multiple statements we cannot be sure
        }
    }
    error_count
}

fn is_step(proto: &Transaction, stmt: StmtId) -> bool {
    matches!(&proto[stmt], Stmt::Step)
}

fn analyze_stmt(
    diag: &mut DiagnosticHandler,
    error_count: &mut u32,
    proto: &Transaction,
    stmt: StmtId,
    mut state: State,
) -> State {
    match &proto[stmt] {
        Stmt::Block(stmts) => {
            for &stmt in stmts {
                state = analyze_stmt(diag, error_count, proto, stmt, state);
            }
            state
        }
        Stmt::Step => {
            state.steps = match state.steps {
                StepCount::Unknown => StepCount::Unknown,
                StepCount::Bounded(old) => StepCount::Bounded(old + 1),
                StepCount::Unbounded => StepCount::Unbounded,
            };
            state.final_stmts = vec![stmt];
            state
        }
        Stmt::Fork => {
            if state.steps == StepCount::Bounded(0) {
                diag.emit_diagnostic_stmt(proto, &stmt, "fork before the first step", Level::Error);
                *error_count += 1;
            }
            state.forks = match state.forks {
                ForkCount::Unknown => ForkCount::Unknown,
                ForkCount::Zero => ForkCount::One(stmt),
                ForkCount::One(prev) => {
                    diag.emit_diagnostic_multi_stmt(
                        proto,
                        &[prev, stmt],
                        &["first fork", "second fork"],
                        "A single protocol may only fork once during its execution.",
                        Level::Error,
                    );
                    *error_count += 1;
                    ForkCount::One(stmt)
                }
            };
            state.final_stmts = vec![stmt];
            state
        }
        Stmt::Assign(_, _) | Stmt::AssertEq(_, _) => {
            state.final_stmts = vec![stmt];
            state
        }
        // control flow
        Stmt::While(_, body) | Stmt::RepeatLoop(_, body) => {
            let mut body_state = analyze_stmt(diag, error_count, proto, *body, State::default());
            if body_state.steps == StepCount::Bounded(0) {
                diag.emit_diagnostic_stmt(
                    proto,
                    &stmt,
                    "Infinite loop detected (no step in loop).",
                    Level::Error,
                );
                *error_count += 1;
            }
            if let ForkCount::One(fork) = body_state.forks {
                diag.emit_diagnostic_multi_stmt(
                    proto,
                    &[stmt, fork],
                    &["loop", "fork"],
                    "A fork inside a while loop might execute more than once!.",
                    Level::Error,
                );
                *error_count += 1;
            } else if body_state.forks == ForkCount::Unknown {
                state.forks = ForkCount::Unknown;
            }
            state.steps = match (body_state.steps, state.steps) {
                (StepCount::Bounded(a), StepCount::Bounded(b)) => StepCount::Bounded(a + b),
                (StepCount::Unknown, _) | (_, StepCount::Unknown) => StepCount::Unknown,
                (StepCount::Unbounded, _) | (_, StepCount::Unbounded) => StepCount::Unbounded,
            };
            // the loop may execute 0 or more times
            state.final_stmts.append(&mut body_state.final_stmts);
            state
        }
        Stmt::IfElse(_, tru, fals) => {
            let after_tru = analyze_stmt(diag, error_count, proto, *tru, state.clone());
            let mut after_fals = analyze_stmt(diag, error_count, proto, *fals, state);
            let steps = if after_tru.steps == after_fals.steps {
                after_tru.steps
            } else {
                StepCount::Unknown
            };
            let forks = if after_tru.forks == after_fals.forks {
                after_tru.forks
            } else {
                ForkCount::Unknown
            };
            let mut final_stmts = after_tru.final_stmts;
            final_stmts.append(&mut after_fals.final_stmts);
            State {
                steps,
                forks,
                final_stmts,
            }
        }
    }
}

/// Analysis State
#[derive(Debug, Clone, PartialEq)]
struct State {
    steps: StepCount,
    forks: ForkCount,
    final_stmts: Vec<StmtId>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            steps: StepCount::Bounded(0),
            forks: ForkCount::Zero,
            final_stmts: vec![],
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum StepCount {
    Unknown,
    Bounded(u32),
    Unbounded,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum ForkCount {
    Unknown,
    Zero,
    One(StmtId),
}
