#!/usr/bin/env sh
exec dune exec --profile=release src/core/tools/vm_repl.exe -- $@
