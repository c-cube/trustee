open Types
open Sigs

type t = subst = {
  ty: expr Var.Map.t;
  m: expr Var.Map.t;
}

let equal a b =
  Var.Map.equal Expr.equal a.ty b.ty && Var.Map.equal Expr.equal a.m b.m

let hash self : int =
  let hm m = CCHash.iter (CCHash.pair Var.hash Expr.hash) (Var.Map.to_iter m) in
  CCHash.combine2 (hm self.ty) (hm self.m)

let[@inline] is_empty self = Var.Map.is_empty self.ty && Var.Map.is_empty self.m

let[@inline] find_exn x s =
  if Expr.is_eq_to_type x.v_ty then
    Var.Map.find x s.ty
  else
    Var.Map.find x s.m

let[@inline] mem x s =
  if Expr.is_eq_to_type x.v_ty then
    Var.Map.mem x s.ty
  else
    Var.Map.mem x s.m

let empty = Expr.subst_empty_
let bind = Expr.subst_bind_
let pp = Expr.subst_pp_
let to_list s = List.rev_append (Var.Map.to_list s.ty) (Var.Map.to_list s.m)
let[@inline] bind' x t s : t = bind s x t
let[@inline] size self = Var.Map.cardinal self.m + Var.Map.cardinal self.ty

let[@inline] to_iter self =
  Iter.append (Var.Map.to_iter self.m) (Var.Map.to_iter self.ty)

let to_string = Fmt.to_string pp

let is_renaming (self : t) : bool =
  let is_renaming_ m =
    try
      let codom =
        Var.Map.fold
          (fun _v e acc ->
            match Expr.view e with
            | E_var u -> Var.Set.add u acc
            | _ -> raise_notrace Exit)
          m Var.Set.empty
      in
      Var.Set.cardinal codom = Var.Map.cardinal m
    with Exit -> false
  in
  is_renaming_ self.ty && is_renaming_ self.m

let[@inline] bind_uncurry_ s (x, t) = bind s x t
let of_list = List.fold_left bind_uncurry_ empty
let of_iter = Iter.fold bind_uncurry_ empty
