open Types
open Sigs

type t = sequent = {
  concl: expr;
  hyps: expr_set;
}

let equal = sequent_eq
let hash = sequent_hash
let make hyps concl : t = { hyps; concl }
let make_l h c = make (Expr_set.of_list h) c
let make_nohyps c : t = make Expr_set.empty c
let[@inline] chash self : Chash.t = Chash.run Expr.Util_chash_.hasher_seq_ self
let[@inline] concl g = g.concl
let[@inline] n_hyps self = Int_map.cardinal self.hyps
let[@inline] hyps g = g.hyps
let[@inline] hyps_iter g = Expr_set.to_iter g.hyps
let[@inline] hyps_l g = Expr_set.to_list g.hyps
let enc = Expr.Util_enc_.enc_seq
let iter_exprs self = Iter.cons (concl self) (hyps_iter self)

let pp out (self : t) : unit =
  if Expr_set.is_empty self.hyps then
    Fmt.fprintf out "@[?-@ %a@]" Expr.pp self.concl
  else
    Fmt.fprintf out "@[<hv>%a@ ?-@ %a@]"
      (pp_iter ~sep:", " Expr.pp)
      (hyps_iter self) Expr.pp self.concl

let to_string = Fmt.to_string pp
