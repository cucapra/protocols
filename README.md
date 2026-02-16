# Protocols
**Protocols** is a DSL for specifying & testing hardware communication protocols at the cycle-level register-transfer level (RTL).
A protocol is described using an `prot` definition containing a sequence of statements:
- `symbol := RHS` assigns the value of the `RHS` expression to the DUT input port `symbol`. The right-hand side expression may be an arbitrary value, represented by `X` ("don't care").
- `step(n)`  advances the clock by `n` cycles (`n > 0`)
- `fork()`  allows for concurrent protocol execution.
- `assert_eq(e1, e2)` tests equality between `e1` and `e2`.
- `while` and `if/else` blocks allow for control flow
- `repeat num_iters iterations { ... }` is a loop that executes for `num_iters` iterations exactly, where `num_iters` must be 
  an input parameter supplied to the `prot`

This repository contains:
- An *interpreter* for the DSL
- A *monitor* tool, which given a specification of a hardware module's communication behavior (written in our DSL)
  and a `.fst` waveform file, infers a transaction-level trace that is consistent with the waveform data 
- Common infrastructure shared between the interpreter & the monitor, such as a parser, type-checker and pretty-printer for our DSL
These tools are all implemented in Rust, with some auxiliary benchmarking scripts written in Python.

## Installation + Build Instructions

**General dependencies**:
Note: the installation instructions below assume a macOS environment.
- Ensure you have Homebrew and `uv` installed
  - If not, follow these instructions to install [Homebrew](https://brew.sh) and [uv](https://docs.astral.sh/uv/getting-started/installation/)
- Run `brew install hyperfine` to install [Hyperfine](https://github.com/sharkdp/hyperfine), a command-line benchmarking tool 
- Run `brew install just` to install [Just](https://github.com/casey/just), a command runner
- Run `uv tool install turnt` to install [Turnt](https://github.com/cucapra/turnt/tree/main), a command-line tool we use for [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html), which compare the output of our tools to expected outputs stored in dedicated files 

**Dependencies for benchmarking the monitor**:
- Run `uv sync` to install the Python dependencies specified in `pyproject.toml` 
- Then, from the top-level directory, run the following scripts (note that they take ~3 minutes to run):
```bash
$ uv run scripts/benchmark_monitor.py      
$ uv run scripts/plot_benchmark_results.py 
```
- This produces a CSV and a scatter plot measuring the performance of the monitor in 
  `benchmark_results/benchmark_results.csv` and `benchmark_results/benchmark_plot.png` respectively

- Some of the benchmarks correspond to real-world bugs taken from the [artifact for *Debugging in the Brave New World of Reconfigurable Hardware* (Ma et al. ASPLOS '22)](https://github.com/efeslab/asplos22-hardware-debugging-artifact) -- these can be found in the `monitor/tests/fpga-debugging` sub-directory 
  (more details in the `README` of the sub-directories corresponding to each bug)

**Interpreter-specific dependencies**:
- Run `brew install yosys` to install [Yosys](https://yosyshq.readthedocs.io/projects/yosys/en/latest/)

**Building the source code**:
- Run `cargo build` to build the Rust code
- Run `just test` to execute all unit tests (`cargo test`) + snapshot tests (via Turnt)
  - To only run the subset of tests for the monitor, run `just monitor` 
- To generate HTML documentation, run `just doc` (this opens Cargo-generated docs in your browser)

## Monitor CLI
The CLI for the monitor can be used as follows:
```bash 
$ cargo run --package protocols-monitor -- --help

Usage: protocols-monitor [OPTIONS] --protocol <PROTOCOLS_FILE> --wave <WAVE_FILE>

Options:
  -p, --protocol <PROTOCOLS_FILE>
          Path to a Protocol (.prot) file
  -w, --wave <WAVE_FILE>
          Path to a waveform trace (.fst, .vcd, .ghw) file
  -i, --instances <INSTANCES>
          A mapping of DUT struct in the protocol file to an instance in the signal trace. Can be used multiple times. Format is: `${instance_name}:${dut_struct_name}
  -v, --verbose...
          Increase logging verbosity
  -q, --quiet...
          Decrease logging verbosity
      --color <COLOR_CHOICE>
          To suppress colors in error messages, pass in `--color never` Otherwise, by default, error messages are displayed w/ ANSI colors [default: auto] [possible values: auto, always, never]
  -d, --display-hex
          If enabled, displays integer literals using hexadecimal notation
      --sample-posedge <SIGNAL_TO_SAMPLE_ON_RISING_EDGE>
          Optional argument which specifies the name of the signal to sample on a rising edge (posedge). If enabled, this flag acts as the "clock" signal for the monitor. Note: the full path to the signal should be passed as this argument, e.g. `uut_rx.clk`, where `uut_rx` is an instance in the signal trace
      --show-waveform-time
          If enabled, displays the start & end waveform time for each inferred transaction
      --time-unit <TIME_UNIT>
          Specifies the time unit for displaying waveform times. Can only be used with --show-waveform-time. Valid options: fs, ps, ns, us, ms, s, auto Default is 'auto' which selects the unit based on the maximum time in the waveform
      --print-num-steps
          Optional flag: if enabled, prints the no. of (logical) steps (i.e. clock cycles) taken by the montior
  -h, --help
          Print help
```

Example usage:
```bash
$ cd monitor/tests
$ cargo run --quiet --package protocols-monitor -- -p adders/add_d1.prot --wave adders/add_d1.fst --instances add_d1:Adder
```

## Interpreter CLI
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

## Syntax highlighting
This repository contains a basic VS Code extension which provides syntax highlighting for `.prot` and `.tx` files 
(the `.tx` file format is used to supply a list of transactions to be executed for the interpreter).

**Installation**:
Add a link to the Protocols VS Code extension directory to your VS Code extensions directory as follows:

```bash
$ cd $HOME/.vscode/extensions
$ ln -s <path to protocols root directory>/tools/vscode protocols.protocols-0.0.1
```

Then, restart VS Code.
