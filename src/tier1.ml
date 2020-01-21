
module Fmt = CCFormat
module T = Core.Expr
module Thm = Core.Thm

type term = Core.Expr.t
type thm = Core.Thm.t

let eq_sym a b =
  (* use leibniz on [λx. a=x] *)
  let p =
    let x = T.new_var "x" (T.ty_exn a) in
    T.lambda x (T.eq (T.var x) a)
  in
  Thm.eq_leibniz a b ~p |> Thm.cut (Thm.refl a)

let eq_trans a b c =
  (* use leibniz on [λx. x=a] *)
  let p =
    let x = T.new_var "x" (T.ty_exn a) in
    T.lambda x (T.eq (T.var x) a)
  in
  let thm_c_a = Thm.eq_leibniz b c ~p |> Thm.cut (eq_sym a b) in
  Thm.cut thm_c_a (eq_sym c a)

let eq_reflect thm =
  let as_trivial_eq t =
    match T.unfold_app t with
    | f, [_a; t; u] when T.equal T.eq_const f && T.equal t u -> Some t
    | _ -> None
  in
  (* find all the [t] such that [(t=t) \in thm.hyps] *)
  let trivial_eqn_members =
    T.Set.fold
      (fun t l -> match as_trivial_eq t with Some x -> T.Set.add x l | None -> l)
      (Thm.hyps thm) T.Set.empty
  in
  Format.printf "trivial: %a@." Fmt.Dump.(list T.pp) (T.Set.elements trivial_eqn_members);
  if T.Set.is_empty trivial_eqn_members then (
    thm
  ) else (
    let refl_l =
      T.Set.fold (fun t l -> Thm.refl t :: l) trivial_eqn_members []
    in
    Thm.cut_l refl_l thm
  )

let eq_proof _ _ = assert false (* TODO *)

(* TODO
let cong_t f g x y : t =
  instantiate cong_ax (Expr.Subst.of_list [f,
   *)
