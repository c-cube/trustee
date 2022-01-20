
module Loc = Trustee_syntax.Loc
module Position = Trustee_syntax.Position
module Loc_input = Trustee_syntax.Loc_input

type t = Loc.t
type ctx = Loc.ctx

let conv_loc_input (self:Loc_input.t) =
  match Loc_input.view self with
  | Loc_input.String s -> Pp_loc.Input.string s

let to_pp_loc ~ctx (self:t) : Pp_loc.loc =
  let off1, off2 = Loc.offsets self in
  Loc.tr_position ~ctx ~left:true off1,
  Loc.tr_position ~ctx ~left:false off2

let pp ~ctx out (self:t) : unit =
  if self == none then ()
  else (
    let input = Loc_input.to_pp_loc_input ctx.input in
    Format.fprintf out "@[<v>%a@ %a@]"
      (pp_compact ~ctx) self
      (Pp_loc.pp ~max_lines:5 ~input) [to_pp_loc ~ctx self]
  )

let pp_l ~ctx out (l:t list) : unit =
  if l=[] then ()
  else (
    let input = Loc_input.to_pp_loc_input ctx.input in
    let locs = List.map (to_pp_loc ~ctx) l in
    Format.fprintf out "@[<v>%a@ %a@]"
      Fmt.(list ~sep:(return ";@ and ") @@ pp_compact ~ctx) l
      (Pp_loc.pp ~max_lines:5 ~input) locs
  )
