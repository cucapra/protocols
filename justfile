# Runs all snapshot tests using Turnt
turnt:
  turnt protocols/tests/*/*/*.tx

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
