
# Trustee [![build](https://github.com/c-cube/trustee/workflows/main/badge.svg)](https://github.com/c-cube/trustee/actions)

A LCF-style kernel of trust intended for certified ATP and proof checking for FOL/HOL.

Brief list of features, current or being developed:

- core API with representation of terms and theorems, in `src/core/kernel.ml`.
  Terms use De Bruijn indices for bound variables, are hashconsed, and polymorphism
  is semi-explicit (i.e. polymorphic constants are applied to types explicitly,
  but type quantifiers are still implicit).
- an OpenTheory library with a parser and a verifier based on trustee,
  in `src/opentheory/`

