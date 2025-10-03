# Only run Turnt tests for the interpreters on the adder examples
adders:
  turnt --env interp $(find protocols/tests/adders -type f -name '*.tx') 

# Only run Turnt tests for the interpreter
interp:
  turnt --env interp $(find . -type f -name '*.tx')

# Only run Turnt tests for the monitor
monitor:
  turnt --env monitor $(find . -type f -name '*.prot')

# Runs all snapshot tests using Turnt
turnt:
  @just interp  
  @just monitor

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
