# Run all Turnt tests for the interpreter
interp:
  turnt --env interp $(find . -type f -name '*.tx') 

# Run all Turnt tests for the monitor
monitor:
  turnt --env monitor $(find . -type f -name '*.prot') 

# Run roundtrip checks (interp -> fst -> monitor) for all transactions
roundtrip:
  turnt --env roundtrip $(find . -type f -name '*.tx')

# Run Turnt tests for the monitor based on the Brave New World artifacts
bnw_monitor:
  turnt --env monitor $(find monitor/tests/fpga-debugging -type f -name '*.prot')   

# Only test Francis's Brave New World (synthetic) examples on the monitor
francis_bnw_monitor:
  turnt --env monitor $(find monitor/tests/brave_new_world_francis -type f -name '*.prot')    

# Only test the monitor on the AXI streaming example (from WAL)
axis:
  turnt --env monitor $(find monitor/tests/wal/advanced -type f -name '*.prot')  

# Only run interpreter tests for the adder examples
adders:
  turnt --env interp $(find protocols/tests/adders -type f -name '*.tx') 

# Only run interpreter tests for the ALU examples
alus:
  turnt --env interp $(find protocols/tests/alus -type f -name '*.tx') 

# Only test the `identities` examples
identities:
  turnt --env interp $(find protocols/tests/identities -type f -name '*.tx')  

# Only test the `multi` examples
multi:
  turnt --env interp $(find protocols/tests/multi -type f -name '*.tx')  

# Only test the `picorv` examples
picorv:
  turnt --env interp $(find examples/picorv32 -type f -name '*.tx')  

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
