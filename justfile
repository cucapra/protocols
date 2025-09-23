# Runs all snapshot tests using Turnt
turnt:
  turnt --env interp $(find . -type f -name '*.tx')
  turnt --env monitor $(find . -type f -name '*.prot')

# Runs all unit tests (via Cargo) & snapshot tests (via Turnt)
test:
  cargo test 
  @just turnt
