// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

use crate::diagnostic::{DiagnosticHandler, Level};
use crate::ir::{ExprId, StmtId, SymbolId, SymbolTable, Transaction};
use crate::serialize::serialize_bitvec;
use baa::BitVecValue;
use std::fmt;

/// Main error type for the scheduler and evaluator system
#[derive(Debug, Clone, PartialEq)]
pub enum ExecutionError {
    /// Evaluation-related errors
    Evaluation(EvaluationError),
    /// Thread execution errors  
    Thread(ThreadError),
    /// Symbol resolution errors
    Symbol(SymbolError),
    /// Assertion failures
    Assertion(AssertionError),
    /// Reached the maximum number of steps
    MaxStepsReached(u32),
}

/// Errors that occur during expression/statement evaluation
#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationError {
    /// Cannot perform operation on DontCare values
    DontCareOperation {
        operation: String,
        context: String,
        expr_id: ExprId,
    },
    /// TODO: Arithmetic errors (e.g., width mismatches in bitvec operations)
    ArithmeticError {
        operation: String,
        details: String,
        expr_id: ExprId,
    },
    /// Conditional evaluation with DontCare
    InvalidCondition {
        stmt_type: String, // "if" or "while"
        expr_id: ExprId,
    },
    /// Invalid slice operation.
    /// self.width() >= msb >= lsb >= 0
    InvalidSlice {
        expr_id: ExprId,
        start: u32,
        end: u32,
        width: u32,
    },
    /// (For monitor only) When the value of an expression on the RHS
    /// of an assignment disagreess with the actual observed trace value
    ValueDisagreesWithTrace {
        expr_id: ExprId,
        value: BitVecValue,
        trace_value: BitVecValue,
        symbol_id: SymbolId,
        symbol_name: String,
        cycle_count: u32,
    },
}

/// Thread-specific execution errors
#[derive(Debug, Clone, PartialEq)]
pub enum ThreadError {
    /// Thread attempted to fork more than once
    DoubleFork {
        thread_idx: usize,
        transaction_name: String,
        first_fork_stmt_id: StmtId,
        second_fork_stmt_id: StmtId,
    },
    /// Thread called `fork()` before `step()`
    ForkBeforeStep {
        thread_idx: usize,
        transaction_name: String,
        stmt_id: StmtId,
    },
    /// Multiple threads trying to assign to same input
    ConflictingAssignment {
        symbol_id: SymbolId,
        symbol_name: String,
        current_value: BitVecValue,
        new_value: BitVecValue,
        thread_idx: usize,
        stmt_id: StmtId,
    },
    /// Thread execution limit exceeded (for infinite loop protection)
    ExecutionLimitExceeded { max_steps: usize },
    /// The thread finished executing without calling `fork()`
    /// (it is required to make exactly one call to `fork()`)
    FinishedWithoutFork {
        thread_idx: usize,
        transaction_name: String,
    },
    /// The last executed statement in the thread is not `step()`
    /// (we explicitly require protocols to end with the
    /// execution of a `step()` statement).
    /// Note that the error message includes info
    /// about what the actual last executed stmt was.
    DidntEndWithStep {
        thread_idx: usize,
        transaction_name: String,
        last_executed_stmt_id: StmtId,
    },
}

/// Symbol resolution and mapping errors
#[derive(Debug, Clone, PartialEq)]
pub enum SymbolError {
    /// Symbol not found in any mapping
    NotFound {
        symbol_id: SymbolId,
        symbol_name: String,
        context: String,
        expr_id: ExprId,
    },
    /// Attempting to assign to read-only symbol
    ReadOnlyAssignment {
        symbol_id: SymbolId,
        symbol_name: String,
        symbol_type: String, // "output", "argument", etc.
        stmt_id: StmtId,
    },
}

/// Assertion failures with detailed information
#[derive(Debug, Clone, PartialEq)]
pub enum AssertionError {
    /// Equality assertion failed
    EqualityFailed {
        expr1_id: ExprId,
        expr2_id: ExprId,
        value1: BitVecValue,
        value2: BitVecValue,
    },
    /// Assertion with DontCare values
    DontCareAssertion { stmt_id: StmtId },
}

// Implement Display for nice error messages
impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExecutionError::Evaluation(e) => write!(f, "Evaluation error: {}", e),
            ExecutionError::Thread(e) => write!(f, "Thread error: {}", e),
            ExecutionError::Symbol(e) => write!(f, "Symbol error: {}", e),
            ExecutionError::Assertion(e) => write!(f, "Assertion error: {}", e),
            ExecutionError::MaxStepsReached(max_steps) => {
                write!(f, "Reached the maximum number of steps: {max_steps}")
            }
        }
    }
}

impl fmt::Display for EvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvaluationError::ValueDisagreesWithTrace {
                expr_id,
                value,
                trace_value,
                symbol_id,
                symbol_name,
                cycle_count,
            } => {
                write!(
                    f,
                    "Attempted to assign value {} (expr_id {}) to {} (symbol_id {}) but the trace value {} at cycle {} is different",
                    serialize_bitvec(value, false),
                    expr_id,
                    symbol_name,
                    symbol_id,
                    serialize_bitvec(trace_value, false),
                    cycle_count
                )
            }
            EvaluationError::DontCareOperation {
                operation, context, ..
            } => {
                write!(
                    f,
                    "Cannot perform {} on DontCare value in {}",
                    operation, context
                )
            }
            EvaluationError::ArithmeticError {
                operation, details, ..
            } => {
                write!(f, "Arithmetic error in {}: {}", operation, details)
            }
            EvaluationError::InvalidCondition { stmt_type, expr_id } => {
                write!(
                    f,
                    "Cannot evaluate {} condition (expr {:?}): value is DontCare",
                    stmt_type, expr_id
                )
            }
            EvaluationError::InvalidSlice {
                expr_id,
                start,
                end,
                width,
            } => {
                write!(
                    f,
                    "Invalid slice operation on expr {:?}: [{}:{}] on width {}",
                    expr_id, start, end, width
                )
            }
        }
    }
}

impl fmt::Display for ThreadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThreadError::DoubleFork {
                thread_idx,
                transaction_name,
                ..
            } => {
                write!(
                    f,
                    "Thread {} (transaction '{}') attempted to fork more than once",
                    thread_idx, transaction_name
                )
            }
            ThreadError::ForkBeforeStep {
                thread_idx,
                transaction_name,
                ..
            } => {
                write!(
                    f,
                    "Thread {} (transaction '{}') called `fork()` before calling `step()`",
                    thread_idx, transaction_name
                )
            }
            ThreadError::ConflictingAssignment {
                symbol_name,
                current_value,
                new_value,
                thread_idx,
                ..
            } => {
                write!(
                    f,
                    "Thread {} attempted conflicting assignment to '{}': current={:?}, new={:?}",
                    thread_idx, symbol_name, current_value, new_value
                )
            }
            ThreadError::ExecutionLimitExceeded { max_steps } => {
                write!(f, "Threads exceeded execution limit of {} steps", max_steps,)
            }
            ThreadError::FinishedWithoutFork {
                thread_idx,
                transaction_name,
            } => {
                write!(
                    f,
                    "Thread {} (transaction '{}') is missing a call `fork()` (all threads must have exactly one `fork()` call)",
                    thread_idx, transaction_name
                )
            }
            ThreadError::DidntEndWithStep {
                thread_idx,
                transaction_name,
                last_executed_stmt_id: _,
            } => {
                write!(
                    f,
                    "The last executed statement in Thread {} (transaction '{}') wasn't `step()` (all threads must end their execution with a call to `step()`)",
                    thread_idx, transaction_name
                )
            }
        }
    }
}

impl fmt::Display for SymbolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolError::NotFound {
                symbol_name,
                context,
                ..
            } => {
                write!(f, "Symbol '{}' not found in {}", symbol_name, context)
            }
            SymbolError::ReadOnlyAssignment {
                symbol_name,
                symbol_type,
                ..
            } => {
                write!(
                    f,
                    "Cannot assign to {} '{}' (read-only)",
                    symbol_type, symbol_name
                )
            }
        }
    }
}

impl fmt::Display for AssertionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AssertionError::EqualityFailed { value1, value2, .. } => {
                write!(f, "Assertion failed: {:?} != {:?}", value1, value2)
            }
            AssertionError::DontCareAssertion { .. } => {
                write!(
                    f,
                    "Assertion failed: cannot assert equality with DontCare values"
                )
            }
        }
    }
}

// Convenience constructors
impl ExecutionError {
    pub fn value_disagrees_with_trace(
        expr_id: ExprId,
        value: BitVecValue,
        trace_value: BitVecValue,
        symbol_id: SymbolId,
        symbol_name: String,
        cycle_count: u32,
    ) -> Self {
        ExecutionError::Evaluation(EvaluationError::ValueDisagreesWithTrace {
            expr_id,
            value,
            trace_value,
            symbol_id,
            symbol_name,
            cycle_count,
        })
    }

    pub fn finished_without_fork(thread_id: usize, transaction_name: String) -> Self {
        ExecutionError::Thread(ThreadError::FinishedWithoutFork {
            thread_idx: thread_id,
            transaction_name,
        })
    }

    pub fn didnt_end_with_step(
        thread_id: usize,
        transaction_name: String,
        last_executed_stmt_id: StmtId,
    ) -> Self {
        ExecutionError::Thread(ThreadError::DidntEndWithStep {
            thread_idx: thread_id,
            transaction_name,
            last_executed_stmt_id,
        })
    }

    pub fn double_fork(
        thread_id: usize,
        transaction_name: String,
        first_fork_stmt_id: StmtId,
        second_fork_stmt_id: StmtId,
    ) -> Self {
        ExecutionError::Thread(ThreadError::DoubleFork {
            thread_idx: thread_id,
            transaction_name,
            first_fork_stmt_id,
            second_fork_stmt_id,
        })
    }

    pub fn fork_before_step(thread_id: usize, transaction_name: String, stmt_id: StmtId) -> Self {
        ExecutionError::Thread(ThreadError::ForkBeforeStep {
            thread_idx: thread_id,
            transaction_name,
            stmt_id,
        })
    }

    pub fn conflicting_assignment(
        symbol_id: SymbolId,
        symbol_name: String,
        current_value: BitVecValue,
        new_value: BitVecValue,
        thread_idx: usize,
        stmt_id: StmtId,
    ) -> Self {
        ExecutionError::Thread(ThreadError::ConflictingAssignment {
            symbol_id,
            symbol_name,
            current_value,
            new_value,
            thread_idx,
            stmt_id,
        })
    }

    pub fn symbol_not_found(
        symbol_id: SymbolId,
        symbol_name: String,
        context: String,
        expr_id: ExprId,
    ) -> Self {
        ExecutionError::Symbol(SymbolError::NotFound {
            symbol_id,
            symbol_name,
            context,
            expr_id,
        })
    }

    pub fn dont_care_operation(operation: String, context: String, expr_id: ExprId) -> Self {
        ExecutionError::Evaluation(EvaluationError::DontCareOperation {
            operation,
            context,
            expr_id,
        })
    }

    pub fn arithmetic_error(operation: String, details: String, expr_id: ExprId) -> Self {
        ExecutionError::Evaluation(EvaluationError::ArithmeticError {
            operation,
            details,
            expr_id,
        })
    }

    pub fn invalid_condition(stmt_type: String, expr_id: ExprId) -> Self {
        ExecutionError::Evaluation(EvaluationError::InvalidCondition { stmt_type, expr_id })
    }

    pub fn invalid_slice(expr_id: ExprId, start: u32, end: u32, width: u32) -> Self {
        ExecutionError::Evaluation(EvaluationError::InvalidSlice {
            expr_id,
            start,
            end,
            width,
        })
    }

    pub fn assertion_failed(
        expr1_id: ExprId,
        expr2_id: ExprId,
        value1: BitVecValue,
        value2: BitVecValue,
    ) -> Self {
        ExecutionError::Assertion(AssertionError::EqualityFailed {
            expr1_id,
            expr2_id,
            value1,
            value2,
        })
    }

    pub fn assertion_dont_care(stmt_id: StmtId) -> Self {
        ExecutionError::Assertion(AssertionError::DontCareAssertion { stmt_id })
    }

    pub fn read_only_assignment(
        symbol_id: SymbolId,
        symbol_name: String,
        symbol_type: String,
        stmt_id: StmtId,
    ) -> Self {
        ExecutionError::Symbol(SymbolError::ReadOnlyAssignment {
            symbol_id,
            symbol_name,
            symbol_type,
            stmt_id,
        })
    }

    pub fn execution_limit_exceeded(max_steps: usize) -> Self {
        ExecutionError::Thread(ThreadError::ExecutionLimitExceeded { max_steps })
    }
}

/// Type alias for Results
pub type ExecutionResult<T> = Result<T, ExecutionError>;

/// Diagnostic emission functions for different error types
pub struct DiagnosticEmitter;

impl DiagnosticEmitter {
    pub fn emit_execution_error(
        handler: &mut DiagnosticHandler,
        error: &ExecutionError,
        transaction: &Transaction,
        symbol_table: &SymbolTable,
    ) {
        match error {
            ExecutionError::Evaluation(eval_err) => {
                Self::emit_evaluation_error(handler, eval_err, transaction, symbol_table);
            }
            ExecutionError::Thread(thread_err) => {
                Self::emit_thread_error(handler, thread_err, transaction, symbol_table);
            }
            ExecutionError::Symbol(symbol_err) => {
                Self::emit_symbol_error(handler, symbol_err, transaction, symbol_table);
            }
            ExecutionError::Assertion(assert_err) => {
                Self::emit_assertion_error(handler, assert_err, transaction, symbol_table);
            }
            ExecutionError::MaxStepsReached(_) => {
                handler.emit_general_message(&format!("{error}"), Level::Error);
            }
        }
    }

    pub fn emit_evaluation_error(
        handler: &mut DiagnosticHandler,
        error: &EvaluationError,
        transaction: &Transaction,
        _symbol_table: &SymbolTable,
    ) {
        match error {
            EvaluationError::DontCareOperation {
                operation,
                context,
                expr_id,
            } => {
                handler.emit_diagnostic_expr(
                    transaction,
                    expr_id,
                    &format!(
                        "Cannot perform {} on DontCare value in {}",
                        operation, context
                    ),
                    Level::Error,
                );
            }
            EvaluationError::ArithmeticError {
                operation,
                details,
                expr_id,
            } => {
                handler.emit_diagnostic_expr(
                    transaction,
                    expr_id,
                    &format!("Arithmetic error in {}: {}", operation, details),
                    Level::Error,
                );
            }
            EvaluationError::InvalidCondition { stmt_type, expr_id } => {
                handler.emit_diagnostic_expr(
                    transaction,
                    expr_id,
                    &format!("Cannot evaluate {} condition: value is DontCare", stmt_type),
                    Level::Error,
                );
            }
            EvaluationError::InvalidSlice {
                expr_id,
                start,
                end,
                width,
            } => {
                handler.emit_diagnostic_expr(
                    transaction,
                    expr_id,
                    &format!(
                        "Invalid slice operation: [{}:{}] on width {}",
                        start, end, width
                    ),
                    Level::Error,
                );
            }
            EvaluationError::ValueDisagreesWithTrace {
                expr_id,
                value,
                trace_value,
                symbol_id,
                symbol_name,
                cycle_count,
            } => {
                let message = format!(
                    "Attempted to assign {:?} to {} (symbol_id {}) but the trace value {:?} at cycle {} is different",
                    value, symbol_name, symbol_id, trace_value, cycle_count
                );
                handler.emit_diagnostic_expr(transaction, expr_id, &message, Level::Error);
            }
        }
    }

    pub fn emit_thread_error(
        handler: &mut DiagnosticHandler,
        error: &ThreadError,
        transaction: &Transaction,
        _symbol_table: &SymbolTable,
    ) {
        match error {
            ThreadError::DoubleFork {
                thread_idx,
                transaction_name,
                first_fork_stmt_id,
                second_fork_stmt_id,
            } => {
                handler.emit_diagnostic_multi_stmt(
                    transaction,
                    &[*first_fork_stmt_id, *second_fork_stmt_id],
                    &["first fork() called here", "second fork() called here"],
                    &format!(
                        "Thread {} (transaction '{}') attempted to fork more than once",
                        thread_idx, transaction_name
                    ),
                    Level::Error,
                );
            }
            ThreadError::ForkBeforeStep {
                thread_idx,
                transaction_name,
                stmt_id,
            } => {
                handler.emit_diagnostic_stmt(
                    transaction,
                    stmt_id,
                    &format!(
                        "Thread {} (transaction '{}') called `fork()` before calling `step()`",
                        thread_idx, transaction_name
                    ),
                    Level::Error,
                );
            }
            ThreadError::ConflictingAssignment {
                symbol_name,
                current_value,
                new_value,
                thread_idx,
                stmt_id,
                ..
            } => {
                handler.emit_diagnostic_stmt(
                    transaction,
                    stmt_id,
                    &format!(
                        "Thread {} attempted conflicting assignment to '{}': current={:?}, new={:?}",
                        thread_idx, symbol_name, current_value, new_value
                    ),
                    Level::Error,
                );
            }
            ThreadError::ExecutionLimitExceeded { max_steps } => {
                // For execution limit exceeded, we don't have a specific statement,
                // so we emit a general diagnostic
                handler.emit_general_message(
                    &format!("Threads exceeded execution limit of {} steps", max_steps),
                    Level::Error,
                );
            }
            ThreadError::FinishedWithoutFork {
                thread_idx,
                transaction_name,
            } => {
                handler.emit_general_message(
                    &format!(
                        "Thread {} (transaction '{}') missing a call to `fork()` (all threads must have exactly one call to `fork()`)", 
                        thread_idx,
                        transaction_name
                    ),
                    Level::Error
                );
            }
            ThreadError::DidntEndWithStep {
                thread_idx,
                transaction_name,
                last_executed_stmt_id,
            } => {
                handler.emit_diagnostic_multi_stmt(
                    transaction,
                    &[*last_executed_stmt_id],
                    &["last statement wasn't `step()`"],
                    &format!(
                        "The last executed statement in Thread {} (transaction '{}') wasn't `step()` (all threads must end their execution with a call to `step()`)", 
                        thread_idx,
                        transaction_name
                    ),
                    Level::Error
                );
            }
        }
    }

    pub fn emit_symbol_error(
        handler: &mut DiagnosticHandler,
        error: &SymbolError,
        transaction: &Transaction,
        _symbol_table: &SymbolTable,
    ) {
        match error {
            SymbolError::NotFound {
                symbol_name,
                context,
                expr_id,
                ..
            } => {
                handler.emit_diagnostic_expr(
                    transaction,
                    expr_id,
                    &format!("Symbol '{}' not found in {}", symbol_name, context),
                    Level::Error,
                );
            }
            SymbolError::ReadOnlyAssignment {
                symbol_name,
                symbol_type,
                stmt_id,
                ..
            } => {
                handler.emit_diagnostic_stmt(
                    transaction,
                    stmt_id,
                    &format!(
                        "Cannot assign to {} '{}' (read-only)",
                        symbol_type, symbol_name
                    ),
                    Level::Error,
                );
            }
        }
    }

    pub fn emit_assertion_error(
        handler: &mut DiagnosticHandler,
        error: &AssertionError,
        transaction: &Transaction,
        _symbol_table: &SymbolTable,
    ) {
        match error {
            AssertionError::EqualityFailed {
                expr1_id,
                expr2_id,
                value1,
                value2,
            } => {
                handler.emit_diagnostic_assertion(transaction, expr1_id, expr2_id, value1, value2);
            }
            AssertionError::DontCareAssertion { stmt_id } => {
                handler.emit_diagnostic_stmt(
                    transaction,
                    stmt_id,
                    "Assertion failed: cannot assert equality with DontCare values",
                    Level::Error,
                );
            }
        }
    }
}
