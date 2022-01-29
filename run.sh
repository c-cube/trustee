#!/bin/sh
OPTS=--profile=release
exec dune exec $(OPTS) src/tools/trustee_bin.exe -- $@
