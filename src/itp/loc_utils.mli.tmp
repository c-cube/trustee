
module Loc = Trustee_syntax.Loc
module Position = Trustee_syntax.Position
module Loc_input = Trustee_syntax.Loc_input

type t = Loc.t
type ctx = Loc.ctx

val conv_loc_input : Loc_input.t -> Pp_loc.Input.t

val to_pp_loc : t -> Pp_loc.loc

val pp : ctx:ctx -> t Fmt.printer
val pp_l : ctx:ctx -> t list Fmt.printer
