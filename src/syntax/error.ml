module Loc = struct
  type t = Loc.t

  let pp out loc = Fmt.fprintf out "@[<v>%a@]@]" Loc.pp loc
end

module E = Trustee_core.Error.Make (Loc)
include E

module C =
  Trustee_core.Error.Conv (Trustee_core.Error) (E)
    (struct
      let conv _ = None
    end)

let of_kernel_err = C.conv
