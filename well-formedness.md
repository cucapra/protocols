# Well-Formedness

Well-formed Protocols programs prevent the following bad things from happening.

## Bad things that can happen at runtime

| **Description**                                                   | **Error enum** (if one exists)       |
|-------------------------------------------------------------------|--------------------------------------|
| Multiple threads try to assign to the same input                  | `ThreadError::ConflictingAssignment` |
| We assign to a read-only symbol                                   | `ThreadError::ReadOnlyAssignment`    |
| A thread attempts to `fork` more than once                        | `ThreadError::DoubleFork`            |
| A thread calls `fork` before calling `step`                       | `ThreadError::ForkBeforeStep`        |
| Performing an operation on a `DontCare`                           | `EvaluationError::DontCareOperation` |
| A `DontCare` value is used as the guard for a loop / if-statement | `EvaluationError::DontCare`          |
| We assert equality with a `DontCare` value                        | `AssertionError::DontCareAssertion`  |
| Width mismatches in bitvec operations                             | `EvaluationError::ArithmeticError`   |
| Invalid slice operations                                          | `EvaluationError::InvalidSlice`      |
| Non-termination (infinite `while` loops)                          | N/A                                  |

**TODOs (implement these as dynamic checks):**
- No `fork`s in program (per 9/30 meeting, a function must have exactly one `fork` somewhere in its body)
- Missing `step` at the end of a function
