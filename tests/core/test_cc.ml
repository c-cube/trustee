
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
  let (===) = app_eq in

  let hyps = [
    (a === (f2 a c));
    (b === (f2 a c));
    (b === (f2 a c));
    (c === (f2 c b));
    (a === (f2 c c));
    ((f2 c (f2 c b)) === (f2 (f2 c c) b));
  ] |> List.map Thm.assume in
  let t = (f2 a b) in
  let u = (f2 a c) in (* goal *)
  let res = CC.prove_cc_eqn ctx hyps t u in
  Format.printf "reg1: %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()

let reg2 _ctx =
  let module M = Make() in
  let open M in

  let c_0 = const a [] in
  let c_1 = const b [] in
  let c_2 = const c [] in
  let f1 x y = app_l (const f2 []) [x;y] in
  let (===) = app_eq in
  let hyps = [
    ((f1 c_1 c_0) = c_2);
    (c_1 === (f1 c_0 c_2));
    (c_1 === (f1 c_1 c_1));
    (c_1 === (f1 c_2 c_0));
    (c_2 === (f1 c_2 c_1));
    (c_0 === (f1 c_2 c_2));
    ((f1 c_1 (f1 c_0 c_2)) === (f1 (f1 c_1 c_0) c_2));
    ((f1 c_2 (f1 c_2 c_1)) === (f1 (f1 c_2 c_2) c_1));
  ] |> List.map Thm.assume in
  let t = f1 c_0 c_1 and u = f1 c_0 c_2 in
  let res = CC.prove_cc_eqn ctx hyps t u in
  Format.printf "reg2: %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()

let suite =
  "cc" >::: [
    "reg1" >:: reg1;
    "reg2" >:: reg2;
  ]

