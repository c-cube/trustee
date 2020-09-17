
# Trustee [![build](https://github.com/c-cube/trustee/workflows/build/badge.svg)](https://github.com/c-cube/trustee/actions)

A LCF-style kernel of trust intended for certified ATP and proof checking for FOL/HOL.

Brief list of features, current or being developed:

- core API with representation of terms and theorems, in `core/src/kernel/`.
  Terms use De Bruijn indices for bound variables, are hashconsed, and polymorphism
  is explicit (i.e. `= : Pi a:type. a -> a -> bool`, rather than ML polymorphism).
- embedded meta-language, custom made, with inline expressions, pattern matching
  against expressions, and proof rules baked in.
  `core/src/meta/prelude.trustee` is the main example for now, and contains
  a basic HOL prelude.
- a small LSP server for the meta-language, in `lsp/`
- a small jupyter kernel for the meta-language, in `jupyter`
- a CLI interface, readline-enabled, in `cli/`.
- an OpenTheory library with a parser and a verifier based on trustee,
  in `opentheory/`

## Meta-language

TODO: explain the basics, going through prelude.

