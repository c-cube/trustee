#!/bin/sh
exec cargo run -p trustee_opentheory --release --example parse_ot -- $@
