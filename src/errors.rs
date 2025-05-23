use std::fmt;
use crate::ir::{SymbolId, StmtId, ExprId};
use baa::BitVecValue;

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
    /// Simulation-related errors
    Simulation(SimulationError),
}

/// Errors that occur during expression/statement evaluation
#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationError {
    /// Cannot perform operation on DontCare values
    DontCareOperation {
        operation: String,
        context: String,
    },
    /// Division by zero or similar arithmetic errors
    ArithmeticError {
        operation: String,
        details: String,
    },
    /// Conditional evaluation with DontCare
    InvalidCondition {
        stmt_type: String, // "if" or "while"
        expr_id: ExprId,
    },
    /// Invalid slice operation
    InvalidSlice {
        expr_id: ExprId,
        start: u32,
        end: u32,
        width: u32,
    },
}

/// Thread-specific execution errors
#[derive(Debug, Clone, PartialEq)]
pub enum ThreadError {
    /// Thread attempted to fork more than once
    DoubleFork {
        thread_id: usize,
        transaction_name: String,
    },
    /// Multiple threads trying to assign to same input
    ConflictingAssignment {
        symbol_id: SymbolId,
        symbol_name: String,
        current_value: BitVecValue,
        new_value: BitVecValue,
        thread_id: usize,
    },
    /// Thread execution limit exceeded (for infinite loop protection)
    ExecutionLimitExceeded {
        thread_id: usize,
        max_steps: u32,
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
    },
    /// Argument symbol not found in symbol table
    ArgumentNotFound {
        arg_name: String,
    },
    /// Attempting to assign to read-only symbol
    ReadOnlyAssignment {
        symbol_id: SymbolId,
        symbol_name: String,
        symbol_type: String, // "output", "argument", etc.
    },
    /// Type mismatch for symbol
    TypeMismatch {
        symbol_id: SymbolId,
        expected_type: String,
        actual_type: String,
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
    DontCareAssertion {
        expr1_id: ExprId,
        expr2_id: ExprId,
    },
    /// Custom assertion with message
    Custom {
        message: String,
        stmt_id: StmtId,
    },
}

/// Simulation and system-level errors
#[derive(Debug, Clone, PartialEq)]
pub enum SimulationError {
    /// Patronus simulator error
    SimulatorError {
        details: String,
    },
    /// System convergence failure
    ConvergenceFailure {
        max_iterations: u32,
        cycle: i32,
    },
    /// Invalid system state
    InvalidState {
        description: String,
    },
    /// Missing system component
    MissingComponent {
        component_type: String,
        name: String,
    },
}

// Implement Display for nice error messages
impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExecutionError::Evaluation(e) => write!(f, "Evaluation error: {}", e),
            ExecutionError::Thread(e) => write!(f, "Thread error: {}", e),
            ExecutionError::Symbol(e) => write!(f, "Symbol error: {}", e),
            ExecutionError::Assertion(e) => write!(f, "Assertion error: {}", e),
            ExecutionError::Simulation(e) => write!(f, "Simulation error: {}", e),
        }
    }
}

impl fmt::Display for EvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvaluationError::DontCareOperation { operation, context } => {
                write!(f, "Cannot perform {} on DontCare value in {}", operation, context)
            }
            EvaluationError::ArithmeticError { operation, details } => {
                write!(f, "Arithmetic error in {}: {}", operation, details)
            }
            EvaluationError::InvalidCondition { stmt_type, expr_id } => {
                write!(f, "Cannot evaluate {} condition (expr {:?}): value is DontCare", stmt_type, expr_id)
            }
            EvaluationError::InvalidSlice { expr_id, start, end, width } => {
                write!(f, "Invalid slice operation on expr {:?}: [{}:{}] on width {}", expr_id, start, end, width)
            }
        }
    }
}

impl fmt::Display for ThreadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThreadError::DoubleFork { thread_id, transaction_name } => {
                write!(f, "Thread {} (transaction '{}') attempted to fork more than once", thread_id, transaction_name)
            }
            ThreadError::ConflictingAssignment { symbol_name, current_value, new_value, thread_id, .. } => {
                write!(f, "Thread {} attempted conflicting assignment to '{}': current={:?}, new={:?}", 
                       thread_id, symbol_name, current_value, new_value)
            }
            ThreadError::ExecutionLimitExceeded { thread_id, max_steps } => {
                write!(f, "Thread {} exceeded execution limit of {} steps", thread_id, max_steps)
            }
        }
    }
}

impl fmt::Display for SymbolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolError::NotFound { symbol_name, context, .. } => {
                write!(f, "Symbol '{}' not found in {}", symbol_name, context)
            }
            SymbolError::ArgumentNotFound { arg_name } => {
                write!(f, "Argument '{}' not found in symbol table", arg_name)
            }
            SymbolError::ReadOnlyAssignment { symbol_name, symbol_type, .. } => {
                write!(f, "Cannot assign to {} '{}' (read-only)", symbol_type, symbol_name)
            }
            SymbolError::TypeMismatch { expected_type, actual_type, .. } => {
                write!(f, "Type mismatch: expected {}, found {}", expected_type, actual_type)
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
                write!(f, "Assertion failed: cannot assert equality with DontCare values")
            }
            AssertionError::Custom { message, .. } => {
                write!(f, "Assertion failed: {}", message)
            }
        }
    }
}

impl fmt::Display for SimulationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimulationError::SimulatorError { details } => {
                write!(f, "Simulator error: {}", details)
            }
            SimulationError::ConvergenceFailure { max_iterations, cycle } => {
                write!(f, "Failed to converge after {} iterations in cycle {}", max_iterations, cycle)
            }
            SimulationError::InvalidState { description } => {
                write!(f, "Invalid simulation state: {}", description)
            }
            SimulationError::MissingComponent { component_type, name } => {
                write!(f, "Missing {} component: {}", component_type, name)
            }
        }
    }
}

// Implement Error trait
impl std::error::Error for ExecutionError {}
impl std::error::Error for EvaluationError {}
impl std::error::Error for ThreadError {}
impl std::error::Error for SymbolError {}
impl std::error::Error for AssertionError {}
impl std::error::Error for SimulationError {}

// Convenience constructors
impl ExecutionError {
    pub fn double_fork(thread_id: usize, transaction_name: String) -> Self {
        ExecutionError::Thread(ThreadError::DoubleFork { thread_id, transaction_name })
    }

    pub fn conflicting_assignment(
        symbol_id: SymbolId,
        symbol_name: String, 
        current_value: BitVecValue,
        new_value: BitVecValue,
        thread_id: usize,
    ) -> Self {
        ExecutionError::Thread(ThreadError::ConflictingAssignment {
            symbol_id,
            symbol_name,
            current_value,
            new_value,
            thread_id,
        })
    }

    pub fn symbol_not_found(symbol_id: SymbolId, symbol_name: String, context: String) -> Self {
        ExecutionError::Symbol(SymbolError::NotFound {
            symbol_id,
            symbol_name,
            context,
        })
    }

    pub fn argument_not_found(arg_name: String) -> Self {
        ExecutionError::Symbol(SymbolError::ArgumentNotFound { arg_name })
    }

    pub fn dont_care_operation(operation: String, context: String) -> Self {
        ExecutionError::Evaluation(EvaluationError::DontCareOperation {
            operation,
            context,
        })
    }

    pub fn invalid_condition(stmt_type: String, expr_id: ExprId) -> Self {
        ExecutionError::Evaluation(EvaluationError::InvalidCondition {
            stmt_type,
            expr_id,
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

    pub fn assertion_dont_care(expr1_id: ExprId, expr2_id: ExprId) -> Self {
        ExecutionError::Assertion(AssertionError::DontCareAssertion {
            expr1_id,
            expr2_id,
        })
    }

    pub fn read_only_assignment(symbol_id: SymbolId, symbol_name: String, symbol_type: String) -> Self {
        ExecutionError::Symbol(SymbolError::ReadOnlyAssignment {
            symbol_id,
            symbol_name,
            symbol_type,
        })
    }
}

// Type alias for Results
pub type ExecutionResult<T> = Result<T, ExecutionError>;