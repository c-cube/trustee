
open Sigs
module K = Kernel
module Su = K.Subst
module E = K.Expr

type subst = K.Subst.t

exception Fail

let[@unroll 2] rec deref subst e =
  match E.view e with
  | E.E_var v ->
    begin match Su.find_exn v subst with
      | exception Not_found -> e
      | e' -> deref subst e'
    end
  | _ -> e

(* occur check: does [v] occur in [e]? *)
let rec occ_check subst v e =
  let e = deref subst e in
  match E.view e with
  | E.E_var v' -> K.Var.equal v v'
  | _ -> E.exists e ~f:(fun _ e' -> occ_check subst v e')

let unif_rec_ subst a b : subst =
  let rec loop subst a b =
    let a = deref subst a in
    let b = deref subst b in

    (* unify types first *)
    let subst = match E.ty a, E.ty b with
      | None, None -> subst
      | Some ty1, Some ty2 when E.equal ty1 ty2 -> subst
      | Some ty1, Some ty2 -> loop subst ty1 ty2
      | Some _, None | None, Some _ -> raise Fail
    in
    match E.view a, E.view b with
    | _ when E.equal a b -> subst
    | E.E_var v1, E.E_var v2 when K.Var.equal v1 v2 -> subst
    | E.E_var v, _ ->
      if occ_check subst v b then raise Fail;
      Su.bind subst v b
    | _, E.E_var v ->
      if occ_check subst v a then raise Fail;
      Su.bind subst v a
    | E.E_const (c1, l1), E.E_const (c2, l2) when K.Const.equal c1 c2 ->
      assert (List.length l1=List.length l2);
      List.fold_left2 loop subst l1 l2
    | E.E_bound_var v1, E.E_bound_var v2 when v1.bv_idx = v2.bv_idx ->
      subst (* types are already unified *)
    | E.E_app (f1, arg1), E.E_app (f2, arg2)
    | E.E_arrow (f1, arg1), E.E_arrow (f2, arg2) ->
      let subst = loop subst f1 f2 in
      loop subst arg1 arg2
    | E.E_lam (_, ty1, bod1), E.E_lam (_, ty2, bod2) ->
      let subst = loop subst ty1 ty2 in
      loop subst bod1 bod2
    | (E.E_kind | E.E_type | E.E_app _ | E.E_arrow _
      | E.E_const _ | E.E_bound_var _ | E.E_lam _ | E.E_box _), _ ->
      raise Fail
  in
  loop subst a b

let unify_exn ?(subst=Su.empty) a b = unif_rec_ subst a b

let unify ?subst a b =
  try Some (unify_exn ?subst a b)
  with Fail -> None

let match_rec_ subst a b : subst =
  let rec loop subst a b =
    (* match types first *)
    let subst = match E.ty a, E.ty b with
      | None, None -> subst
      | Some ty1, Some ty2 when E.equal ty1 ty2 -> subst
      | Some ty1, Some ty2 -> loop subst ty1 ty2
      | Some _, None | None, Some _ -> raise Fail
    in
    match E.view a, E.view b with
    | E.E_var v1, _ when Su.mem v1 subst ->
      (* follow substitution but only once *)
      let t = Su.find_exn v1 subst in
      if E.equal t b then subst else raise Fail
    | E.E_var v1, E.E_var v2 when K.Var.equal v1 v2 -> subst
    | E.E_var v, _ -> Su.bind subst v b
    | E.E_const (c1, l1), E.E_const (c2, l2) when K.Const.equal c1 c2 ->
      assert (List.length l1=List.length l2);
      List.fold_left2 loop subst l1 l2
    | E.E_bound_var v1, E.E_bound_var v2 when v1.bv_idx = v2.bv_idx ->
      subst (* types are already matched *)
    | E.E_app (f1, arg1), E.E_app (f2, arg2)
    | E.E_arrow (f1, arg1), E.E_arrow (f2, arg2) ->
      let subst = loop subst f1 f2 in
      loop subst arg1 arg2
    | E.E_lam (_, ty1, bod1), E.E_lam (_, ty2, bod2) ->
      let subst = loop subst ty1 ty2 in
      loop subst bod1 bod2
    | (E.E_kind | E.E_type | E.E_app _ | E.E_arrow _
      | E.E_const _ | E.E_bound_var _ | E.E_lam _ | E.E_box _), _ ->
      raise Fail
  in
  loop subst a b

let match_exn ?(subst=Su.empty) a b = match_rec_ subst a b

let match_ ?subst a b =
  try Some (match_exn ?subst a b)
  with Fail -> None

let alpha_equiv_exn ?subst a b =
  let subst = match_exn ?subst a b in
  if K.Subst.is_renaming subst then subst
  else raise Fail

let alpha_equiv ?subst a b =
  try Some (alpha_equiv_exn ?subst a b)
  with Fail -> None

let is_alpha_equiv ?subst a b : bool =
  Option.is_some (alpha_equiv ?subst a b)
