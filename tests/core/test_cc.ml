
open Helpers
open OUnit2

module CC = Trustee_core.Congruence_closure

(* from the following PO:
    `cl (- a = (f2 a c)),
        (- b = (f2 a c)),
        (- c = (f2 c b)),
        (- a = (f2 c c)),
        (- (f2 c (f2 c b)) = (f2 (f2 c c) b)),
        (+ (f2 a b) = (f2 a c))))`
   *)
let reg1 _ctx =
  let module M = Make() in
  let open M in

  let a = const a [] in
  let b = const b [] in
  let c = const c [] in
  let f2 x y = app_l (const f2 []) [x;y] in
  let eq = app_eq in

  let hyps = [
    Thm.assume (eq a (f2 a c));
    Thm.assume (eq b (f2 a c));
    Thm.assume (eq b (f2 a c));
    Thm.assume (eq c (f2 c b));
    Thm.assume (eq a (f2 c c));
    Thm.assume (eq (f2 c (f2 c b)) (f2 (f2 c c) b));
  ] in
  let t = (f2 a b) in
  let u = (f2 a c) in (* goal *)
  let res = CC.prove_cc_eqn ctx hyps t u in
  Format.printf "reg1@.";
  assert_bool "is-res" (CCOpt.is_some res);
  ()


let suite =
  "cc" >::: [
    "reg1" >:: reg1;
  ]

