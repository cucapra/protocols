default: lint build test

# At the moment, we only run Turnt on the tests which have been configured for Turnt
turnt-tests:
  cd protocols/tests && turnt adders/*/*.tx && turnt multipliers/mult_d2/*.tx && turnt identities/identity_d2/*.tx

build:
  cargo build

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  just turnt-tests

# Applies Clippy's suggestions & formats the code 
lint:
  cargo clippy --fix
  cargo fmt 
