
build:
	@cargo build --release

all: build test

lsp:
	@cargo build --release -p trustee_lsp
.PHONY: lsp

install_lsp:
	@make -C lsp install

clean:
	@cargo clean

check:
	@cargo check --all

doc:
	@cargo doc

test:
	@cargo test

.PHONY: doc clean
