#!/bin/sh
OPTS="--profile=release -j 3"
exec dune exec $(OPTS) src/tools/trustee_bin.exe -- $@
