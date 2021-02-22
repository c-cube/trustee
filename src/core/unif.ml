
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

type op = O_unif | O_match

let u_rec op subst a b : subst =
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
      Su.bind v b subst
    | _, E.E_var v when op == O_unif ->
      if occ_check subst v a then raise Fail;
      Su.bind v a subst
    | E.E_const (c1, l1), E.E_const (c2, l2) when K.Const.equal c1 c2 ->
      assert (List.length l1=List.length l2);
      List.fold_left2 loop subst l1 l2
    | E.E_bound_var v1, E.E_bound_var v2 when v1.bv_idx = v2.bv_idx ->
      subst (* types are already unified *)
    | E.E_app (f1, arg1), E.E_app (f2, arg2)
    | E.E_arrow (f1, arg1), E.E_arrow (f2, arg2) ->
      let subst = loop subst f1 f2 in
      loop subst arg1 arg2
    | E.E_lam (ty1, bod1), E.E_lam (ty2, bod2) ->
      let subst = loop subst ty1 ty2 in
      loop subst bod1 bod2
    | (E.E_kind | E.E_type | E.E_app _ | E.E_arrow _
      | E.E_const _ | E.E_bound_var _ | E.E_lam _), _ ->
      raise Fail
  in
  loop subst a b

let unify_exn ?(subst=Su.empty) a b = u_rec O_unif subst a b

let unify ?subst a b =
  try Some (unify_exn ?subst a b)
  with Fail -> None

let match_exn ?(subst=Su.empty) a b = u_rec O_match subst a b

let match_ ?subst a b =
  try Some (match_exn ?subst a b)
  with Fail -> None
