(** {1 Core functions to manipulate Terms and Theorems} *)

open Trustee_kot

module Fmt = CCFormat
module T = Expr

type term = T.t
type thm = Thm.t

(** [app_term f (F |- t=u)] is [F |- (f t)=(f u)] *)
let app1_term f th : Thm.t = Thm.cong (Thm.refl f) th

(** [app_term x (F |- f=g)] is [F |- (f x)=(g x)] *)
let app2_term x th = Thm.cong th (Thm.refl x)

let eq_trans a b c =
  Thm.trans (Thm.assume (T.eq a b)) (Thm.assume (T.eq b c))

let eq_sym a b =
  (* from [a=b] we get [(a=b) = (a=b)] *)


  (* use congruence on [λx. b=x] and [a=b],
     leading to [a=b |- (λx.b=x) a = (λx.b=x) b],
     then use beta to get [a=b |- (b=a)=(b=b)].
     Then EQ_MP with [|-b=b] (refl b) to get [a=b |- b=a] *)
  let x = T.new_var "x" (T.ty_exn a) in
  let f = T.lambda x (T.eq b @@ T.var x) in
  let thm_fa_is_ba, _b_eq_a = Thm.beta f a in
  let thm_fb_is_bb, b_eq_b = Thm.beta f b in
  let c = Thm.trans thm_fa_is_ba (Thm.assume (T.eq (T.app f a) (T.app f b))) in
  Format.printf "@[c: %a@]@." Thm.pp c;
  let c = Thm.cong (Thm.refl f) (Thm.assume (T.eq a b)) in
  Format.printf "@[c: %a@]@." Thm.pp c;

  (*
  let c = Thm.trans c thm_fa_is_ba in
  let c = Thm.bool_eq (T.eq 

  Format.printf "c: %a@." Thm.pp c;
     *)

  assert false

(*
  let p =
    let x = T.new_var "x" (T.ty_exn a) in
    T.lambda x (T.eq (T.var x) a)
  in
  Thm.eq_leibniz a b ~p |> Thm.cut (Thm.refl a)
   *)

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
    T.Set.fold
      (fun t thm -> Thm.cut (Thm.refl t) thm) trivial_eqn_members thm
  )

let cong_fol f l1 l2 =
  if List.length l1 <> List.length l2 then (
    errorf_ (fun k->k "cong_fol: arity mismatch")
  );
  let rec aux thm l1 l2 = match l1, l2 with
    | [], [] -> thm
    | [], _ | _, [] -> assert false
    | x :: l1', y :: l2' ->
      let thm = Thm.cong thm (Thm.assume @@ T.eq x y) in
      aux thm l1' l2'
  in
  aux (Thm.refl f) l1 l2

let eq_proof _ _ = assert false (* TODO *)

(* TODO
let cong_t f g x y : t =
  instantiate cong_ax (Expr.Subst.of_list [f,
   *)
