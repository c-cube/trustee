OPTS?=-j 3 --profile=release

all:
	@dune build @all $(OPTS)

WATCH?=@all
watch:
	@dune build $(OPTS) $(WATCH) -w

test:
	@dune runtest $(OPTS) --force --no-buffer

clean:
	@dune clean

doc:
	@dune build @doc

KERNEL_DIR=$${HOME}/.local/share/jupyter/kernels/trustee_script/

install_kernel:
	mkdir -p $(KERNEL_DIR)
	cp data/kernel.json $(KERNEL_DIR)/

