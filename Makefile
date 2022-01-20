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
