
module Expr = Trustee_kot.Expr
module Thm = Trustee_kot.Thm
module Fmt = CCFormat

let pp_list ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

type t = {
  hyps: (string * Thm.t) list;
  concl: Expr.t;
}

let concl self = self.concl
let hyps self = self.hyps
let make ?(hyps=[]) concl : t = {hyps; concl}

let pp out (self:t) : unit =
  let pp_hyp out (name,thm) =
    if name="" then Expr.pp out (Thm.concl thm)
    else Fmt.fprintf out "@[<2>%s: %a@]" name Expr.pp (Thm.concl thm)
  in
  Fmt.fprintf out "@[<v>%a@ |------@ %a@]"
    (pp_list pp_hyp) self.hyps Expr.pp self.concl
