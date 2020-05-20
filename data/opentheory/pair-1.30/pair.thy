name: pair
version: 1.30
description: Product types
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
show: "Data.Bool"
show: "Data.Pair"

def {
  package: pair-def-1.24
  checksum: 0b8284a82166c2c2a0228c493c551fc3c497d43c
}

thm {
  import: def
  package: pair-thm-1.31
  checksum: 3a1a48fb8c9b98348986a95a38415f0e0b2c2985
}

main {
  import: def
  import: thm
}
