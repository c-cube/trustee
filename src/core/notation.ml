
open Sigs

type fixity = Fixity.t
type t = {
  fixs: fixity Str_map.t;
} [@@unboxed]


let[@inline] find self s = Str_map.get s self.fixs
let[@inline] find_or_default self s = Str_map.get_or s self.fixs ~default:Fixity.normal
let[@inline] declare s f self = {fixs=Str_map.add s f self.fixs}

let empty = {fixs=Str_map.empty}

let pp out (self:t) : unit =
  let pppair out (s,f) = Fmt.fprintf out "(@[%s %a@])" s Fixity.pp f in
  Fmt.fprintf out "(@[notations@ (@[%a@])@])"
    Fmt.(iter pppair) (Str_map.to_iter self.fixs)

module Ref = struct
  type notation = t
  type nonrec t = notation ref
  let create() = ref empty
  let of_notation n = ref n
  let find self s = find !self s
  let find_or_default self s = find_or_default !self s
  let declare self s f = self := declare s f !self
  let pp out self = pp out !self
end


let empty_hol =
  empty
  |> declare "=" (Fixity.infix 18)
  |> declare "select" (Fixity.binder 10)
  |> declare "==>" (Fixity.binder 12)
