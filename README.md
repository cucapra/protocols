# Protocols
**Protocols** is a DSL for specifying & testing hardware designs at the cycle-level RTL level.
A protocol is described using an `fn` definition containing a list of imperative statements:
- `symbol := RHS` assigns the value of the `RHS` expression to the DUT input port `symbol`. The right-hand side expression may be an arbitrary value, represented by `X` ("don't care").
- `step(n)`  advances the clock by `n` cycles.
- `fork()`  allows for concurrent protocol execution.
- `assert_eq(e1, e2)` tests equality between `e1` and `e2`.
- `while` and `if/else` blocks allow for control flow

**Build instructions**:
- Run `brew install yosys` to install Yosys
- Run `uv tool install turnt` to install [Turnt](https://github.com/cucapra/turnt/tree/main) 
  - Note: this presumes you already have `uv` installed (if not, [follow these instructions](https://docs.astral.sh/uv/getting-started/installation/#pypi))
- Run `cargo build` to build
- Run `cargo test` to execute all unit tests
- To run a snapshot test, from the [`protocols/tests`](./protocols/tests/) subdirectory, do `turnt tests/adders/adder_d1/add_d1.tx`
- Note: to view the expected results of some snapshot tests (in `.out` files), install the [ANSI Colors](https://marketplace.visualstudio.com/items?itemName=iliazeus.vscode-ansi) VS Code extension
  - Some tests expect the interpreter to fail, and error messages are displayed using ANSI escape sequences, which is why the VS Code extension is handy

**CLI**:
The interpreter has a CLI, which can be invoked as follows:
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
$ cargo run -- --verilog protocols/tests/adders/adder_d1/add_d1.v \
        --protocol protocols/tests/adders/adder_d1/add_d1.prot \
        -t protocols/tests/adders/adder_d1/add_d1.tx \
        --verbose
```
