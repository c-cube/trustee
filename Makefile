
build:
	@cargo build --release

all: build test

clean:
	@cargo clean

check:
	@cargo check

doc:
	@cargo doc

test:
	@cargo test --release

.PHONY: doc clean
