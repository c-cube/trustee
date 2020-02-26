name: set-size
version: 1.60
description: Finite set cardinality
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: natural
requires: pair
requires: set-def
requires: set-finite
requires: set-fold
requires: set-thm
show: "Data.Bool"
show: "Data.Pair"
show: "Number.Natural"
show: "Set"

def {
  package: set-size-def-1.33
  checksum: 2db12e8f076e243552f308ccdb3fe545d2d876c6
}

thm {
  import: def
  package: set-size-thm-1.66
  checksum: d4594633cdd6a4e4ca308b3acb774d670bed3723
}

main {
  import: def
  import: thm
}
