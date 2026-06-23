# Runt-based snapshot testing: catalog-driven workflow

## TL;DR for contributors

- **Add/edit a test:** edit `scripts/test_catalog.py`, run
  `python3 scripts/generate_runt_configs.py`, then `runt -s runt/<suite>` to
  save the golden `.expect` file. Commit the catalog, the regenerated
  `runt.toml`, and the new `.expect`.
- **Run tests:** `just runt` (or `runt runt/interp`, `runt runt/monitor`,
  `runt runt/graph_interp`).
- **never** hand-write `runt.toml` 

## How it works

```
scripts/test_catalog.py -> scripts/generate_runt_configs.py
-> runt/<suite>/runt.toml -> runt  
->  <test_dir>/expects/<stem>.<runner>.expect 
```

The catalog holds only the facts that can't be derived from the `.prot`/`.tx`/
`.v` files themselves (how a test wires up to its protocol/RTL and its expected
outcome). Everything else — commands, expect-file names, which protocol features
a test uses — is computed by the generator.

## The catalog (`scripts/test_catalog.py`)

Two tables. Omit optional fields when empty.

### `TX_CASES` — interpreter / graph-interpreter cases, keyed by `.tx` path

```python
"tests/adders/adder_d0/add_combinational.tx": {
    "protocol": "tests/adders/adder_d0/add_d0.prot",   # the .prot it runs against
    "verilog": ("tests/adders/adder_d0/add_d0.v",),     # RTL (optional)
    "top": "picorv32_pcpi_mul",                          # top module (optional)
    "expect": "pass",                                    # "pass" or a failure class
    # "max_steps": 8,        (optional)
    # "extra_args": ("--skip-static-step-fork-checks",),  (optional)
},
```

`expect` is `"pass"`, or a failure-class string for expected failures
(`comb_dependency`, `assertion_mismatch`, `assignment_conflict`,
`fork_protocol_error`, `static_type_error`, `static_well_formedness`,
`max_steps`).

### `MONITOR_CASES` — monitor cases, keyed by a unique id

Monitors are keyed by id (not path) because many cases can share one `.prot`
(e.g. the antmicro cases differ only by waveform).

```python
"tests.wishbone.wishbone.monitor": {
    "protocol": "tests/wishbone/wishbone.monitor.prot",
    "wave": "tests/wishbone/reqwalker.vcd",
    "instances": ("TOP.reqwalker:WBSubordinate",),
    "expect": "pass",
    "extra_args": ("--sample-posedge", "TOP.reqwalker.i_clk"),
    # "max_steps" / "timeout_secs": (optional)
},
```

### Programatically Generating Cases
The large antmicro family is generated from a list of trace stems via a small
helper at the bottom of the file. I reccomend you do something like this whenever we have to procedurally generate a number of cases.

## The suites

Exactly three, and their union covers every test:

| suite | runner | contents |
|---|---|---|
| `interp` | interpreter | every `TX_CASES` entry |
| `monitor` | monitor | every `MONITOR_CASES` entry |
| `graph_interp` | graph interpreter | the subset of passing tx whose protocol has no `for`/`repeat` loop |

Each suite is defined using a series of filters over the test cases. Since this is all python, you can do arbitrary filtering. 

## How features are detected (graph_interp selection)

The graph interpreter can't yet handle `for-in`/`repeat` loops. Instead of
tracking an allowlist, the generator asks the protocol compiler which constructs
each protocol uses:

```
cargo run --bin protocols-cli -- -p <file>.prot constructs
```

This prints the AST-derived constructs per protocol definition. A passing tx is
included in `graph_interp` iff its protocol uses no `for_in_loop`/`repeat_loop`.
This reads the real AST using an [EnumDiscriminant](https://docs.rs/strum/latest/strum/derive.EnumDiscriminants.html) macro, which means if you add new `Stmt` types to the AST or add new test cases, there is no maintenance overhead.

## Expected failures and timeouts

- **Expected failures** (`expect` != `"pass"`): the runner prints its diagnostic
  to stdout and exits non-zero; Runt captures both the message and the exit code
  in the `.expect` snapshot, so failure output is diff-tested like everything
  else.
- **Expected timeouts**: unfortunately runt can not handle an *expected* timeout. a few monitor cases are non-terminating by design and
  set `timeout_secs`. The generated command wraps them in a small timeout script 
  timeout (kills the process group, exits 124) which we can expect in Runt.

## auto-generated naming of .expect files

- Expect file: `<test_dir>/expects/<stem>.<runner>.expect`
  (e.g. `add_combinational.interp.expect`). The `<runner>` keeps a `.tx`'s
  `interp` and `graph_interp` goldens from colliding; monitor antmicro cases are
  named by their waveform stem.
- The generator errors out if two cases would ever map to the same expect file
  with different commands, so collisions can't silently clobber a golden.


## CI

In `.github/workflows/test.yml`, the `tests` job:

1. builds the workspace,
2. **regenerates the configs and fails if they differ from what's checked in**
   (`python3 scripts/generate_runt_configs.py` + `git diff`) — so a stale
   `runt.toml` can't slip through,
3. runs `cargo test`,
4. runs `runt/interp`, `runt/graph_interp`, `runt/monitor`.

Runt is installed in CI from our fork
(`cargo install --git https://github.com/Nikil-Shyamsunder/runt.git`), which adds
the custom expect file naming behavior these suites rely on.

## Repo-level changes

- **Consolidated tests.** All snapshot tests now live under a common `tests/`
  (and `examples/`) tree instead of being scattered per-crate, with one catalog
  describing them.
- **De-duplicated metadata.** The catalog no longer stores anything derivable: a
  single `protocol` pointer per tx (was a redundant id + path), one `expect`
  field (was separate expected/return-code/failure-class), and no
  protocol-feature table (features are computed on the fly). Implementation-
  specific error strings are no longer pinned in the catalog.
- **Removed the old turnt framework.** Deleted the `turnt.toml` files and the
  stale `.out`/`.err` fixtures it used; Runt `.expect` files are the single
  source of goldens.
- **Trimmed the suite set** to `interp` / `monitor` / `graph_interp` (dropped the
  redundant per-directory and combined suites — they were strict subsets).
- **Simplified the generator**: generated commands are self-contained
  (`cd <repo-root> && cargo run … <test>`), and expect-file naming was reduced to
  `<stem>.<runner>` now that every case has a unique key.

## Files that should be reviewed by hand  

`scripts/test_catalog.py` - hand-maintained catalog (the only thing you edit to add tests) 

`scripts/generate_runt_configs.py` - generates `runt/*/runt.toml` from the catalog when you want to make a new suite

`.github/workflows/test.yml` - CI: config-freshness check + the three suites |

`ast.rs` and `cli/main.rs` - a few changes that allow us to print all the constructs in a `.prot` file