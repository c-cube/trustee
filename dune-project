(lang dune 1.11)
(generate_opam_files true)

(name trustee)
(source (github c-cube/trustee))
(license MIT)
(authors "Simon Cruanes")
(maintainers "simon.cruanes.2007@m4x.org")

(package
 (name trustee)
 (synopsis "LCF proof checker")
 (description "TODO")
 (depends dune containers (alcotest :with-test) (ocaml (>= "4.04"))))
