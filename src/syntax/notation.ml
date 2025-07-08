open Common_
module N_map = Str_map

type fixity = Fixity.t
type t = { fixs: fixity N_map.t } [@@unboxed]

let[@inline] find self name = N_map.get name self.fixs
let[@inline] find_name self name = find self name

let[@inline] find_or_default self s =
  N_map.get_or s self.fixs ~default:Fixity.normal

let[@inline] find_name_or_default self name = find_or_default self name
let[@inline] declare s f self = { fixs = N_map.add s f self.fixs }
let empty = { fixs = N_map.empty }

let pp out (self : t) : unit =
  let pp_pair out (n, f) = Fmt.fprintf out "(@[%s %a@])" n Fixity.pp f in
  Fmt.fprintf out "(@[notations@ (@[%a@])@])"
    Fmt.(iter pp_pair)
    (N_map.to_iter self.fixs)

let empty_hol =
  empty
  |> declare "=" (Fixity.infix 40)
  |> declare "select" (Fixity.binder 30)
  |> declare "==>" (Fixity.rassoc 15)

module Ref = struct
  type notation = t
  type nonrec t = notation ref

  let create () = ref empty
  let create_hol () = ref empty_hol
  let of_notation n = ref n
  let find self s = find !self s
  let find_or_default self s = find_or_default !self s
  let declare self s f = self := declare s f !self
  let pp out self = pp out !self
end
