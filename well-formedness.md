# Well-Formedness

This document details the well-formedness constraints on `.prot` programs:

## Static checks 
- Local variable definitions in function bodies are forbidden.
- All function arguments are immutable. 
- We also check that assignments, assertions and conditionals (`if` and `while`) 
abide by the grammars discussed below. These grammars are designed in order to 
make it tractable to reconstruct transactions from a waveform and `.prot` file
(which is what the monitor does)

### Grammar for assignments
- In assignments `LHS := RHS`, `LHS` & `RHS` must conform to the following grammar:

```
LHS := DUT input port
RHS ::= rhs_expr
   | rhs_expr[i:j]          (bit-slice)
   | rhs_expr ++ rhs_expr   (where `++` is concatenation)

rhs_expr ::= DUT input port | input parameter to a function | constant
```
- We also permit `LHS := X`, where `LHS` still a DUT input port & `X` is a distinguished `DontCare` symbol 
that indicates the value of `LHS` is irrelevant at the current cycle.

### Grammar for assertions
- In assertions (`assert_eq(LHS, RHS)` or `assert_eq(RHS, LHS)`), `LHS` & `RHS` must conform to the following grammar:

```
LHS, RHS ::= arg_expr
   | arg_expr[i:j]          (bit-slice)
   | arg_expr ++ arg_expr   (where `++` is concatenation)

arg_expr ::= DUT output port | output parameter of a function | constant
```
- This grammar is slightly different from the grammar for assignments: assertions refer to *output* parameters / DUT ports,
whereas assignments refer to *input* parameters / DUT ports 

### Grammar for conditions (guards) in `if`-statements & `while`-loops
In `if (cond) {...} then {...}` and `while (cond) {...}`, 
the condition `cond` must conform to the following grammar:

```
cond ::= 
  | !cond                       (negation)
  | cond_expr == cond_expr      (equality)

cond_expr ::= 
  | DUT output port 
  | constant 
  | cond_expr[i:j]              (bit-slice)
  | cond_expr ++ cond_expr      (concatenation)
```
- In the future, we may allow the grammar for `cond` to include other comparison operators (e.g. `<=` and `<`)

## Runtime checks

| **Error condition**                                                                                                          | **Error enum** (if one exists)       |
|------------------------------------------------------------------------------------------------------------------------------|--------------------------------------|
| Multiple threads try to assign to the same input                                                                             | `ThreadError::ConflictingAssignment` |
| We assign to a read-only symbol                                                                                              | `ThreadError::ReadOnlyAssignment`    |
| A thread attempts to `fork` more than once                                                                                   | `ThreadError::DoubleFork`            |
| A thread calls `fork` before calling `step`                                                                                  | `ThreadError::ForkBeforeStep`        |
| A thread finished executing without calling `fork()` (all threads are required to make exactly one call to `fork()`)         | `ThreadError::FinishedWithoutFork`   |
| The last executed statement in a thread is not `step()` (threads are required to finish their execution by calling `step()`) | `ThreadError::DidntEndWithStep`      |
| Performing an operation on a `DontCare`                                                                                      | `EvaluationError::DontCareOperation` |
| A `DontCare` value is used as the guard for a loop / if-statement                                                            | `EvaluationError::DontCare`          |
| We assert equality with a `DontCare` value                                                                                   | `AssertionError::DontCareAssertion`  |
| Width mismatches in bitvec operations                                                                                        | `EvaluationError::ArithmeticError`   |
| Invalid slice operations                                                                                                     | `EvaluationError::InvalidSlice`      |
| Non-termination (infinite `while` loops)                                                                                     | N/A                                  |
