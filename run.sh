#!/bin/sh
OPTS="--profile=release -j 3 --display=quiet"
exec dune exec "$OPTS" src/tools/trustee_bin.exe -- $@
