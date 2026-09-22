(lang dune 3.16)

(name CoverageType)

(generate_opam_files true)

(source
 (github username/reponame))

(pin
 (package
  (name zutils))
 (url
  "git+https://github.com/OCamlRefinementType/zutils.git#c664146e9c0b76a9db9ec42e9c16b9c6b3c1cbf4"))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name CoverageType)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  core
  core_unix
  ppx_optcomp
  ppx_compare
  ppx_sexp_conv
  ppx_inline_test
  ppx_assert
  ppx_deriving
  ppx_here
  ppx_deriving_yojson
  zutils
  spectrum)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
