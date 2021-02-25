
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
let occ_check subst v e =
  let rec loop bnd e =
    let e = deref subst e in
    match E.view e with
    | E.E_var v' -> not (K.Var.Set.mem v' bnd) && K.Var.equal v v'
    | _ ->
      E.exists bnd e ~bind:(fun bnd v -> K.Var.Set.add v bnd) ~f:loop
  in
  loop K.Var.Set.empty e

type op = O_unif | O_match

let u_rec op subst a b : subst =
  let bnd_count_ = ref 0 in

  (* one of [a] and [b] is a bound variable, so this only succeeds if
     the other one is one too, and if they have the same unique identifier *)
  (* @param bnd map from bound vars to unique (temporary) identifiers *)
  let rec loop bnd1 bnd2 subst a b =
    let a = deref subst a in
    let b = deref subst b in

    (* unify types first *)
    let subst = match E.ty a, E.ty b with
      | None, None -> subst
      | Some ty1, Some ty2 when E.equal ty1 ty2 -> subst
      | Some ty1, Some ty2 -> loop bnd1 bnd2 subst ty1 ty2
      | Some _, None | None, Some _ -> raise Fail
    in
    match E.view a, E.view b with
    | _ when E.equal a b -> subst
    | E.E_var v1, E.E_var v2 when K.Var.equal v1 v2 -> subst
    | E.E_var v1, _ when K.Var.Map.mem v1 bnd1 ->
      (* can only succeed if [b] is the same bound variable *)
      begin match E.view b with
        | E.E_var v2 ->
          let same_bnd =
            try K.Var.Map.find v1 bnd1 = K.Var.Map.find v2 bnd2
            with Not_found -> false
          in
          if same_bnd then subst else raise Fail
        | _ -> raise Fail
      end
    | _, E.E_var v when K.Var.Map.mem v bnd2 -> raise Fail (* [a] is not bound *)
    | E.E_var v, _ ->
      if occ_check subst v b then raise Fail;
      Su.bind subst v b
    | _, E.E_var v when op == O_unif ->
      if occ_check subst v a then raise Fail;
      Su.bind subst v a
    | E.E_const (c1, l1), E.E_const (c2, l2) when K.Const.equal c1 c2 ->
      assert (List.length l1=List.length l2);
      List.fold_left2 (loop bnd1 bnd2) subst l1 l2
    | E.E_app (f1, arg1), E.E_app (f2, arg2)
    | E.E_arrow (f1, arg1), E.E_arrow (f2, arg2) ->
      let subst = loop bnd1 bnd2 subst f1 f2 in
      loop bnd1 bnd2 subst arg1 arg2
    | E.E_lam (v1, bod1), E.E_lam (v2, bod2) ->
      let subst = loop bnd1 bnd2 subst v1.v_ty v2.v_ty in

      (* now map both locals to a fresh integer *)
      let n = !bnd_count_ in
      incr bnd_count_;
      let bnd1 = K.Var.Map.add v1 n bnd1 in
      let bnd2 = K.Var.Map.add v2 n bnd2 in

      loop bnd1 bnd2 subst bod1 bod2
    | (E.E_kind | E.E_type | E.E_app _ | E.E_arrow _
      | E.E_const _ | E.E_lam _), _ ->
      raise Fail
  in
  loop K.Var.Map.empty K.Var.Map.empty subst a b

let unify_exn ?(subst=Su.empty) a b = u_rec O_unif subst a b

let unify ?subst a b =
  try Some (unify_exn ?subst a b)
  with Fail -> None

let match_exn ?(subst=Su.empty) a b = u_rec O_match subst a b

let match_ ?subst a b =
  try Some (match_exn ?subst a b)
  with Fail -> None
