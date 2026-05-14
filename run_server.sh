#!/bin/bash

eval $( opam env )
exec dune exec --profile=release ./src/opentheory/tool/trustee_ot.exe \
  -- --serve --port 8089 --proof-zip ot-data.zip $@

