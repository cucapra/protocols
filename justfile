# At the moment, we only run Turnt on the tests which have been configured for Turnt
turnt-tests:
  cd protocols/tests && turnt adders/*/*.tx && turnt multipliers/mult_d2/*.tx && turnt identities/identity_d2/*.tx && turnt multi/multi_data/*.tx && turnt multi/multi2const/*.tx && turnt multi/multi2multi/*.tx

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt-tests
