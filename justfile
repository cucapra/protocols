default: lint build test

build:
  cargo build

test:
  cargo test 

lint:
  cargo clippy --fix --allow-dirty
  cargo fmt 
