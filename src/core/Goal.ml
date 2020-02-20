module Fmt = CCFormat

module Make(C : Core.S) = struct
  open C.KoT

  let pp_list ppx out l =
    Fmt.(list ~sep:(return "@ ") ppx) out l

  type t = {
    hyps: (string * Expr.t) list;
    concl: Expr.t;
  }

  let concl self = self.concl
  let hyps self = self.hyps
  let make ?(hyps=[]) concl : t = {hyps; concl}

  let pp out (self:t) : unit =
    let pp_hyp out (name,e) =
      if name="" then Expr.pp out e
      else Fmt.fprintf out "@[<2>%s: %a@]" name Expr.pp e
    in
    Fmt.fprintf out "@[<v>%a@ |------@ %a@]"
      (pp_list pp_hyp) self.hyps Expr.pp self.concl
end
