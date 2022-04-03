#!/bin/sh
exec dune exec --profile=release src/opentheory/tool/trustee_ot.exe -- $@
