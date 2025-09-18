# At the moment, we only run Turnt on the tests which have been configured for Turnt
turnt:
  cd protocols/tests && turnt adders/*/*.tx && turnt multipliers/*/*.tx && turnt identities/*/*.tx && turnt multi/*/*.tx && turnt counters/*.tx && turnt inverters/*.tx

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
