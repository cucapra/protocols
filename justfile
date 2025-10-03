# Only run interpreter tests for the adder examples
adders:
  turnt --env interp $(find protocols/tests/adders -type f -name '*.tx') 

identities:
  turnt --env interp $(find protocols/tests/identities -type f -name '*.tx')  

# Run all Turnt tests for the interpreter
interp:
  turnt --env interp $(find . -type f -name '*.tx')

# Run all Turnt tests for the monitor
monitor:
  turnt --env monitor $(find . -type f -name '*.prot')

# Runs all Turnt tests for both the interpreter & monitor
turnt:
  @just interp  
  @just monitor

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
