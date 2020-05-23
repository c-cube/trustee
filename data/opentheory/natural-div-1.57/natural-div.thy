name: natural-div
version: 1.57
description: Natural number division
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: natural-add
requires: natural-def
requires: natural-mult
requires: natural-numeral
requires: natural-order
requires: natural-thm
show: "Data.Bool"
show: "Number.Natural"

def {
  package: natural-div-def-1.41
  checksum: 1e26516a418173d187d0ab5926c6d346d3dd9188
}

thm {
  import: def
  package: natural-div-thm-1.60
  checksum: dd2a4139b07ddac76763336dd454bf352b210235
}

main {
  import: def
  import: thm
}
