# Runs all snapshot tests using Turnt
turnt:
  turnt $(find . -type f -name '*.tx')

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
