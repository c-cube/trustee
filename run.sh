#!/bin/sh
exec dune exec --profile=release src/tools/trustee_bin.exe -- $@
