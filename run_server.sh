#!/bin/bash
cd $HOME/w/trustee
eval $( opam env )
exec dune exec --profile=release ./src/opentheory/tool/trustee_ot.exe \
  -- --dir vendor/opentheory/data/theories/ --serve --port 8089 --check-all $@

