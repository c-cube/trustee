OPTS?=-j 3 --profile=release

all:
	@dune build @all $(OPTS)

opentheory:
	@dune build @src/opentheory/all $(OPTS)

WATCH?=@all
watch:
	@dune build $(OPTS) $(WATCH) -w

test:
	@dune runtest $(OPTS) --force --no-buffer

clean:
	@dune clean

doc:
	@dune build @doc

format:
	@dune fmt --auto-promote

.PHONY: format clean

KERNEL_DIR=$${HOME}/.local/share/jupyter/kernels/trustee_script/

install_kernel:
	mkdir -p $(KERNEL_DIR)
	cp data/kernel.json $(KERNEL_DIR)/

