(lang dune 3.0)

(generate_opam_files true)

(name trustee)

(authors "Simon Cruanes")

(maintainers "Simon Cruanes")

(homepage "https://github.com/c-cube/trustee/")

(source
 (github "c-cube/trustee"))

(bug_reports "https://github.com/c-cube/trustee/issues")

(version 0.1)

(package
 (name trustee)
 (synopsis "Kernel of trust and proof assistant for HOL")
 (license MIT)
 (tags
  (logic proof HOL assistant))
 (depends
  (containers
   (and
    (>= 3.3)
    (< 4.0)))
  (pp_loc
   (and
    (>= 2.0)
    (< 3.0)))
  (iter
   (>= 1.0))
  (ocaml
   (>= 4.08.0))
  (trace
   (>= 0.10))
  sha
  (ppx_deriving :with-test)
  (qtest :with-test)
  (ounit2 :with-test)
  (qcheck :with-test)
  (odoc :with-doc)))

(package
 (name trustee-opentheory)
 (synopsis "Opentheory parser and checker using Trustee")
 (license MIT)
 (depends
  (containers
   (and
    (>= 3.6)
    (< 4.0)))
  (trustee
   (= :version))
  (tiny_httpd
   (>= 0.16))
  lru
  logs
  trace
  trace-tef
  camlzip
  tiny_httpd_camlzip
  (odoc :with-doc)))

