# Runs the Runt snapshot suites that together cover every test
runt:
  runt runt/interp
  runt runt/monitor
  runt runt/graph_interp

# Runs all unit tests (via Cargo) & snapshot tests (via Runt)
test:
  cargo test
  @just runt

# Builds HTML documentation by running `cargo doc`
doc:
  cargo doc --document-private-items --workspace --no-deps --open
