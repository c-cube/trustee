
all:
	@dune build @all --profile=release


# must create this manually, since dune won't take it as a dependency
# see https://github.com/ocaml/dune/issues/1407
cargo-config-file:
	@mkdir -p .cargo
	@cat cargo-config > .cargo/config

CAML_LIB ?= $(shell ocamlc -where)

# TODO: generate flags from dune?
build-rust-stubs: cargo-config-file
	@if [ "$$(uname)" = "Darwin" ]; then \
		RUSTFLAGS='-L $(CAML_LIB) -lcamlrun' cargo build --release --frozen ; \
	else \
		cargo build --release --frozen ; \
  	fi
