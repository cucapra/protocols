# Protocols
**Protocols** is a DSL for specifying & testing hardware designs at the cycle-level RTL level.
A protocol is described using an `fn` definition containing a list of imperative statements:
- `symbol := RHS` assigns the value of the `RHS` expression to the DUT input port `symbol`. The right-hand side expression may be an arbitrary value, represented by `X` ("don't care").
- `step(n)`  advances the clock by `n` cycles.
- `fork()`  allows for concurrent protocol execution.
- `assert_eq(e1, e2)` tests equality between `e1` and `e2`.
- `while` and `if/else` blocks allow for control flow

This repository contains:
- An *interpreter* for the DSL
- A *monitor* tool, which given a specification of a hardware module's communication behavior (written in our DSL)
  and a `.fst` waveform file, infers a transaction-level trace that is consistent with the waveform data 
- Common infrastructure shared between the interpreter & the monitor, such as a parser, type-checker and pretty-printer for our DSL
These tools are all implemented in Rust, with some auxiliary benchmarking scripts written in Python.

**General dependencies**:
Note: the installation instructions below assume a macOS environment.
- Ensure you have Homebrew and `uv` installed 
  - If not, [follow these instructions to install uv](https://docs.astral.sh/uv/getting-started/installation/))
- Run `brew install just` to install [Just](https://github.com/casey/just), a command runner
- Run `uv tool install turnt` to install [Turnt](https://github.com/cucapra/turnt/tree/main), which we use for [snapshot testing](https://www.cs.cornell.edu/~asampson/blog/turnt.html)
  - Note: this presumes you already have `uv` installed (if not, [follow these instructions](https://docs.astral.sh/uv/getting-started/installation/#pypi))
- Run `npm install -g faucet` to install [Faucet](https://github.com/tape-testing/faucet), which summarizes test outputs from Turnt in a human-readable manner

**Dependencies for benchmarking the monitor**:
- Run `uv sync` to install the Python dependencies specified in `pyproject.toml` 
- Then, from the top-level directory, run the following scripts:
```bash
$ uv run scripts/benchmark_monitor.py
$ uv run scripts/plot_benchmark_results.py 
```
- This produces a CSV and a scatter plot measuring the performance of the monitor in 
  `benchmark_results.benchmark_results.csv` and `benchmark_results.benchmark_plot.png` respectively

**Interpreter-specific dependencies**:
- Run `brew install yosys` to install [Yosys](https://yosyshq.readthedocs.io/projects/yosys/en/latest/)

**Building the source code**:
- Run `cargo build` to build
- Run `just test` to execute all unit tests (`cargo test`) + snapshot tests (via Turnt)
- Run `just turnt` to only run Turnt snapshot tests
- To generate HTML documentation, run `just doc` (this opens Cargo-generated docs in your browser)

**Interpreter CLI**:
The interpreter has a CLI, which can be invoked as follows:
```bash
$ cargo run --package protocols-interp -- --help

Usage: protocols-interp [OPTIONS] --verilog <VERILOG_FILE> --protocol <PROTOCOLS_FILE> --transactions <TRANSACTIONS_FILE>

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
          (Optional) Name of the waveform file (.fst) in which to save results
  -v, --verbose...
          Prints logs / debugging information to stdout
  -h, --help
          Print help
```

Example usage:

```bash
$ cargo run --package protocols-interp -- --verilog protocols/tests/adders/adder_d1/add_d1.v \
        --protocol protocols/tests/adders/adder_d1/add_d1.prot \
        -t protocols/tests/adders/adder_d1/both_threads_pass.tx \
        --verbose
```

### Syntax highlighting
This repository contains a basic VS Code extension which provides syntax highlighting for `.prot` and `.tx` files.

**Installation**:
Add a link to the Protocols VSCode extension directory to your VSCode extensions directory as follows:

```bash
cd $HOME/.vscode/extensions
ln -s <path to protocols root directory>/tools/vscode protocols.protocols-0.0.1
```

Then, restart VSCode.
