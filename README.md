# Protocols
**Protocols** is a DSL for specifying & testing hardware designs at the cycle-level RTL level.
A protocol is described using an `fn` definition containing a list of imperative statements:
- `symbol := RHS` assigns the value of the `RHS` expression to the DUT input port `symbol`. The right-hand side expression may be an arbitrary value, represented by `\dontcare`.
- `step($n$)`  advances the clock by `n` cycles.
- `fork()`  allows for concurrent protocol execution.
- `assert\_eq($e_1$, $e_2$)` tests equality between `e_1` and `e_2`.
- `while` and `if/else` blocks allow for control flow

**Build instructions**:
- Run `brew install yosys` to install Yosys
- Run `cargo build` to build
- Run `cargo test` to execute all tests

**CLI**:
The interpreter has a CLI, which can be invoked as follows
```bash
$ cargo run -- --help

Usage: protocols [OPTIONS] --verilog <VERILOG_FILE> --protocol <PROTOCOLS_FILE> --transactions <TRANSACTIONS_FILE>

Options:
      --verilog <VERILOG_FILE>
          Path to a Verilog (.v) file
  -p, --protocol <PROTOCOLS_FILE>
          Path to a Protocol (.prot) file
  -t, --transactions <TRANSACTIONS_FILE>
          Path to a Transactions (.tx) file
  -m, --module <MODULE_NAME>
          Name of the top-level module (if one exists)
  -f, --fst <WAVEFORM_FILE>
          Name of the waveform file (.fst) in which to save results [default: trace.fst]
  -v, --verbose...
          Prints logs / debugging information to stdout
  -h, --help
          Print help
```

Example usage:

```bash
$ cargo run -- --verilog tests/adders/adder_d1/add_d1.v -p "tests/adders/adder_d1/add_d1.prot" -t "tests/adders/adder_d1/add_d1.tx"
```
