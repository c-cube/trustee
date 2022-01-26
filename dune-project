(lang dune 2.0)
(using menhir 2.0)
(generate_opam_files true)

(name trustee)
(authors "Simon Cruanes")
(maintainers "Simon Cruanes")
(homepage "https://github.com/c-cube/trustee/")
(source (github "c-cube/trustee"))
(bug_reports "https://github.com/c-cube/trustee/issues")

(package
  (name trustee)
  (synopsis "Kernel of trust and proof assistant for HOL")
  (license MIT)
  (tags (logic proof HOL assistant))
  (depends
    (dune (>= "2.0"))
    (containers (and (>= 3.3) (< 4.0)))
    (iter (>= 1.0))
    (ocaml (>= 4.08.0))
    (qtest :with-test)
    (ounit2 :with-test)
    (qcheck :with-test)
    (odoc :with-doc)))

(package
  (name trustee-opentheory)
  (synopsis "Opentheory parser and checker using Trustee")
  (license MIT)
  (depends
    (dune (>= "2.0"))
    (containers (and (>= 3.0) (< 4.0)))
    (trustee (= :version))
    (odoc :with-doc)))

(package
  (name trustee-itp)
  (synopsis "Trustee-powered interactive theorem prover")
  (depends
    (dune (>= "2.0"))
    (containers (and (>= 3.0) (< 4.0)))
    containers-thread
    pp_loc
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
    (trustee (= "version"))
    (trustee-itp (= "version"))
    lsp
    logs
    (linol (and (>= 0.4) (< 0.5)))
    (ocaml (>= 4.06.0))
    (odoc :with-doc)))

