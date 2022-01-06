
build:
	@cargo build --release

all: build test

lsp:
	@cargo build --release -p trustee_lsp
.PHONY: lsp

clean:
	@cargo clean

check:
	@cargo check --all

doc:
	@cargo doc

test:
	@cargo test

.PHONY: doc clean
