name: set
version: 1.85
description: Set types
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
requires: pair
show: "Data.Bool"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Set"

def {
  package: set-def-1.52
  checksum: a130d0c53fa5eb070f40b36d2fe74d500eab3a65
}

thm {
  import: def
  package: set-thm-1.75
  checksum: c43911526d059f66c9b310e0d8ec3d240f590cb4
}

finite {
  import: def
  import: thm
  package: set-finite-1.62
  checksum: c44d5d78292567a24e72224e595d92c8e534db5c
}

fold {
  import: thm
  import: finite
  package: set-fold-1.46
  checksum: 24c4f848d83eec4cebfaa91096efe5bdb3015b6e
}

size {
  import: def
  import: thm
  import: finite
  import: fold
  package: set-size-1.60
  checksum: e760befbcc7021676d7ac0da6438dfc2439f1f34
}

main {
  import: def
  import: thm
  import: finite
  import: fold
  import: size
}
