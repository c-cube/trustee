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
    (pp_loc (and (>= 1.0) (< 2.0)))
    (iter (>= 1.0))
    (ocaml (>= 4.08.0))
    sha
    cbor
    (ppx_deriving :with-test)
    (qtest :with-test)
    (ounit2 :with-test)
    (qcheck :with-test)
    (odoc :with-doc)))

(package
  (name trustee-script)
  (synopsis "Script language around Trustee")
  (license MIT)
  (depends
    (containers (and (>= 3.6) (< 4.0)))
    (trustee (= :version))
    ppx_deriving
    menhir
    pp_loc
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

(package
  (name trustee-itp)
  (synopsis "Trustee-powered interactive theorem prover")
  (depends
    (containers (and (>= 3.0) (< 4.0)))
    containers-thread
    logs
    cmdliner
    (ocaml (>= 4.08.0))
    (odoc :with-doc)))

(package
  (name trustee-lsp)
  (synopsis "LSP server for trustee")
  (license MIT)
  (tags (logic proof HOL assistant))
  (depends
    (dune (>= "2.0"))
    (containers (and (>= 3.0) (< 4.0)))
    (trustee (= :version))
    (trustee-itp (= :version))
    lsp
    logs
    (linol (and (>= 0.4) (< 0.5)))
    (ocaml (>= 4.06.0))
    (odoc :with-doc)))

