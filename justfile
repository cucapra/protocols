# Runs the Runt snapshot suites that together cover every test
runt:
  cargo build --offline --package protocols-interp --package protocols-monitor --package graph-interp --package bi
  runt --max-futures 1 runt/interp
  runt --max-futures 1 runt/monitor
  runt --max-futures 1 runt/bi
  runt --max-futures 1 runt/graph_interp
  runt --max-futures 1 runt/waveform

# Runs all unit tests (via Cargo) & snapshot tests (via Runt)
test:
  cargo test
  @just runt

# Builds HTML documentation by running `cargo doc`
doc:
  cargo doc --document-private-items --workspace --no-deps --open
