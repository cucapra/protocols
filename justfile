# Run all turnt --parallel tests for the interpreter in parallel
# (Output is piped through Faucet to clearly distinguish passing/failing tests)
interp:
  turnt --parallel --env interp $(find . -type f -name '*.tx') | faucet

# Run all turnt --parallel tests for the monitor in parallel
monitor:
  turnt --parallel --env monitor $(find . -type f -name '*.prot') | faucet

# Run turnt --parallel tests for the monitor based on the Brave New World artifacts
bnw_monitor:
  turnt --parallel --env monitor $(find monitor/tests/fpga-debugging -type f -name '*.prot') | faucet  

# Only test Francis's Brave New World (synthetic) examples on the monitor
francis_bnw_monitor:
  turnt --parallel --env monitor $(find monitor/tests/brave_new_world_francis -type f -name '*.prot') | faucet   

# Only test the monitor on the AXI streaming example (from WAL)
axis:
  turnt --parallel --env monitor $(find monitor/tests/wal/advanced -type f -name '*.prot') | faucet 

# Only run interpreter tests for the adder examples
adders:
  turnt --parallel --env interp $(find protocols/tests/adders -type f -name '*.tx') | faucet

# Only run interpreter tests for the ALU examples
alus:
  turnt --parallel --env interp $(find protocols/tests/alus -type f -name '*.tx') | faucet

# Only test the `identities` examples
identities:
  turnt --parallel --env interp $(find protocols/tests/identities -type f -name '*.tx') | faucet 

# Only test the `multi` examples
multi:
  turnt --parallel --env interp $(find protocols/tests/multi -type f -name '*.tx') | faucet 

# Only test the `picorv` examples
picorv:
  turnt --parallel --env interp $(find examples/picorv32 -type f -name '*.tx') | faucet 

# Runs all turnt --parallel tests for both the interpreter & monitor
turnt:
  @just interp  
  @just monitor

# Runs all unit tests (via Cargo) & snapshot tests (via turnt --parallel)
test:
  cargo test 
  @just turnt --parallel

# Builds HTML documentation by running `cargo doc`
doc:
  cargo doc --document-private-items --workspace --no-deps --open
