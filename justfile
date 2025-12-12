# Run all Turnt tests for the interpreter in parallel
# (Output is piped through Faucet to clearly distinguish passing/failing tests)
interp:
  turnt --env interp --parallel $(find . -type f -name '*.tx') | faucet

# Run all Turnt tests for the monitor in parallel
monitor:
  turnt --env monitor --parallel $(find . -type f -name '*.prot') | faucet

# Run Turnt tests for the monitor based on the Brave New World artifacts
bnw_monitor:
  turnt --env monitor --parallel $(find monitor/tests/fpga-debugging -type f -name '*.prot') | faucet  

# Only test Francis's Brave New World (synthetic) examples on the monitor
francis_bnw_monitor:
  turnt --env monitor --parallel $(find monitor/tests/brave_new_world_francis -type f -name '*.prot') | faucet   

# Only test the monitor on the AXI streaming example (from WAL)
axis:
  turnt --env monitor --parallel $(find monitor/tests/wal/advanced -type f -name '*.prot') | faucet 

# Only run interpreter tests for the adder examples
adders:
  turnt --env interp --parallel $(find protocols/tests/adders -type f -name '*.tx') | faucet

# Only run interpreter tests for the ALU examples
alus:
  turnt --env interp --parallel $(find protocols/tests/alus -type f -name '*.tx') | faucet

# Only test the `identities` examples
identities:
  turnt --env interp --parallel $(find protocols/tests/identities -type f -name '*.tx') | faucet 

# Only test the `multi` examples
multi:
  turnt --env interp --parallel $(find protocols/tests/multi -type f -name '*.tx') | faucet 

# Only test the `picorv` examples
picorv:
  turnt --env interp --parallel $(find examples/picorv32 -type f -name '*.tx') | faucet 

# Runs all Turnt tests for both the interpreter & monitor
turnt:
  @just interp  
  @just monitor

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt

# Builds HTML documentation by running `cargo doc`
doc:
  cargo doc --document-private-items --workspace --no-deps --open
