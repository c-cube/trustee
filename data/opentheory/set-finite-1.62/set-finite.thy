name: set-finite
version: 1.62
description: Finite sets
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
requires: pair
requires: set-def
requires: set-thm
show: "Data.Bool"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Set"

def {
  package: set-finite-def-1.37
  checksum: 5ea93dfad7fc9a0d9031fe5f50c09ab0778e31c4
}

thm {
  import: def
  package: set-finite-thm-1.68
  checksum: d1c44780608e6904de387e5472013073d66c7c6f
}

main {
  import: def
  import: thm
}
