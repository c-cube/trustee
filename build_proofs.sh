#!/bin/bash

eval $( opam env )
exec dune exec --profile=release ./src/opentheory/tool/trustee_ot.exe \
  -- --dir vendor/opentheory/data/ --build-zip ot-data.zip $@

