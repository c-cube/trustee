(** {1 Core functions to manipulate Terms and Theorems} *)

open Trustee_kot

module Fmt = CCFormat
module T = Expr

type term = T.t
type thm = Thm.t

(** [app_term f (F |- t=u)] is [F |- (f t)=(f u)] *)
let app1_term f th : Thm.t = Thm.congr (Thm.refl f) th

(** [app_term x (F |- f=g)] is [F |- (f x)=(g x)] *)
let app2_term x th = Thm.congr th (Thm.refl x)

let eq_lhs t = fst @@ T.unfold_eq_exn t
let eq_rhs t = snd @@ T.unfold_eq_exn t

(** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c].
    We reimplement it here to show it's redundant. *)
let cut' th1 th2 =
  let c1 = Thm.concl th1 in
  if T.Set.mem c1 (Thm.hyps th2) then (
    (* [F1,F2 |- b=c] *)
    let th_bc = Thm.bool_eq_intro th1 th2 in
    (* booleq with [F1 |- b] to get [F1,F2 |- c] *)
    Thm.bool_eq ~eq:th_bc th1
  ) else (
    errorf_
      (fun k->k"cut: conclusion of %a@ does not appear in hypothesis of %a"
          Thm.pp th1 Thm.pp th2)
  )

let eq_trans a b c =
  Thm.trans (Thm.assume (T.eq a b)) (Thm.assume (T.eq b c))

(** [sym (F |- t=u)] is [F |- u=t] *)
let sym (th:Thm.t) : Thm.t =
  try
    (* start with [F |- t=u].
       now by left-congruence with [refl(=)], [F |- ((=) t) = ((=) u)].
       by right-congruence with [refl(t)], [F |- (((=) t) t) = (((=) u) t)].
       in other words, [F |- (t=t)=(u=t)].
       Just do bool_eq_elim with [|- t=t] (refl(t)) and we're done. *)
    let t, u = T.unfold_eq_exn (Thm.concl th) in
    let refl_t = Thm.refl t in
    let th_tequ_eq_ueqt =
      Thm.congr
        (Thm.congr (Thm.refl @@ T.app T.eq_const (T.ty_exn u)) th)
        refl_t
    in
    Thm.bool_eq ~eq:th_tequ_eq_ueqt refl_t
  with Error msg ->
    error_wrapf_ msg (fun k->k"(@[in@ sym %a])" Thm.pp th)

(* [eq_sym t u] is [t=u |- u=t] *)
let eq_sym a b = sym (Thm.assume (T.eq a b))
  (* from [a=b] we get [(a=b) = (a=b)] *)

(*
  let p =
    let x = T.new_var "x" (T.ty_exn a) in
    T.lambda x (T.eq (T.var x) a)
  in
  Thm.eq_leibniz a b ~p |> Thm.cut (Thm.refl a)
   *)

(** [eq_reflect (F, a=a, b=b |- t)] is [F |- t].
    Trivial equations in hypothesis are removed. *)
let eq_reflect thm =
  let as_trivial_eq t =
    match T.unfold_eq_exn t with
    | t, u when T.equal t u -> Some t
    | _ -> None
    | exception Error _ -> None
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
    T.Set.fold
      (fun t thm -> Thm.cut (Thm.refl t) ~lemma:thm) trivial_eqn_members thm
  )

let cong_fol f l1 l2 =
  if List.length l1 <> List.length l2 then (
    errorf_ (fun k->k "cong_fol: arity mismatch")
  );
  let rec aux thm l1 l2 = match l1, l2 with
    | [], [] -> thm
    | [], _ | _, [] -> assert false
    | x :: l1', y :: l2' ->
      let thm = Thm.congr thm (Thm.assume @@ T.eq x y) in
      aux thm l1' l2'
  in
  aux (Thm.refl f) l1 l2

let eq_proof _ _ = assert false (* TODO *)

(* TODO
let cong_t f g x y : t =
  instantiate cong_ax (Expr.Subst.of_list [f,
   *)
