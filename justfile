# Run all Runt tests for the interpreter
interp:
  runt --max-futures 1 -j 1 runt/interp

# Run all Runt tests for the monitor
monitor:
  runt runt/monitor

# Run Runt tests for the monitor based on the Brave New World artifacts
bnw_monitor:
  runt runt/bnw_monitor

# Only test Francis's Brave New World (synthetic) examples on the monitor
francis_bnw_monitor:
  runt runt/francis_bnw_monitor

# Only test the monitor on the AXI streaming example (from WAL)
axis:
  runt runt/axis

# Only run interpreter tests for the adder examples
adders:
  runt --max-futures 1 -j 1 runt/adders

# Only run graph-interpreter tests that are explicitly enabled
graph_interp:
  runt runt/graph_interp

# Only run interpreter tests for the ALU examples
alus:
  runt --max-futures 1 -j 1 runt/alus

# Only test the `identities` examples
identities:
  runt --max-futures 1 -j 1 runt/identities

# Only test the `multi` examples
multi:
  runt --max-futures 1 -j 1 runt/multi

# Only test the `picorv` examples
picorv:
  runt --max-futures 1 -j 1 runt/picorv

# Runs all Runt tests for both the interpreter & monitor
runt:
  @just interp  
  @just monitor

# Runs all unit tests (via Cargo) & snapshot tests (via Runt)
test:
  cargo test 
  @just runt

# Builds HTML documentation by running `cargo doc`
doc:
  cargo doc --document-private-items --workspace --no-deps --open
