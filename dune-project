(lang dune 2.0)
(using menhir 2.0)
(generate_opam_files true)

(name trustee)
(authors "Simon Cruanes")
(maintainers "Simon Cruanes")
(homepage "https://github.com/c-cube/trustee/")
(source (github "c-cube/trustee"))
(bug_reports "https://github.com/c-cube/trustee/issues")
(version 0.1)

(package
  (name trustee)
  (synopsis "Kernel of trust and proof assistant for HOL")
  (license MIT)
  (tags (logic proof HOL assistant))
  (depopts
    sqlite3)
  (depends
    (containers (and (>= 3.3) (< 4.0)))
    (iter (>= 1.0))
    (ocaml (>= 4.08.0))
    sha
    cbor
    (ppx_deriving :with-test)
    (ounit2 :with-test)
    (qcheck :with-test)
    (odoc :with-doc)))

(package
  (name trustee-opentheory)
  (synopsis "Opentheory parser and checker using Trustee")
  (license MIT)
  (depends
    (containers (and (>= 3.6) (< 4.0)))
    (trustee (= :version))
    (tiny_httpd (>= 0.12))
    logs
    (odoc :with-doc)))

