
open Helpers
open OUnit2

module CC = Trustee_core.Congruence_closure

module Make() = struct
  include Make()

  let a = const a []
  let b = const b []
  let c = const c []
  let f1 =
    let f1 = const (new_const "f1" (tau @-> tau @-> tau)) [] in
    fun x y -> app_l f1 [x;y]
  let f2 x y = app_l (const f2 []) [x;y]

  let c_0 = const (new_const "c_0" tau) []
  let c_1 = const (new_const "c_1" tau) []
  let c_2 = const (new_const "c_2" tau) []

  let c6 = const (new_const "c6" tau) []
  let c7 = const (new_const "c7" tau) []
  let c8 = const (new_const "c8" tau) []
  let c9 = const (new_const "c9" tau) []
end

let debug_ = ref false

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
  if !debug_ then Format.printf "reg1: %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()

let reg2 _ctx =
  let module M = Make() in
  let open M in

  let hyps = [
    ((f2 c_1 c_0) === c_2);
    (c_1 === (f2 c_0 c_2));
    (c_1 === (f2 c_1 c_1));
    (c_1 === (f2 c_2 c_0));
    (c_2 === (f2 c_2 c_1));
    (c_0 === (f2 c_2 c_2));
    ((f2 c_1 (f2 c_0 c_2)) === (f2 (f2 c_1 c_0) c_2));
    ((f2 c_2 (f2 c_2 c_1)) === (f2 (f2 c_2 c_2) c_1));
  ] |> List.map Thm.assume in
  let t = f2 c_0 c_1 and u = f2 c_0 c_2 in
  let res = CC.prove_cc_eqn ctx hyps t u in
  if !debug_ then Format.printf "reg2: %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()

let reg3 _ctx =
  let module M = Make() in
  let open M in

  let hyps = [
    (c_1 === (f2 c_0 c_2));
    (c_0 === (f2 c_1 c_0));
    (c_1 === (f2 c_2 c_0));
    (c_2 === (f2 c_2 c_1));
    (c_0 === (f2 c_2 c_2));
    (c_2 === c6);
    (c_1 === c7);
    (c_2 === c8);
    (c_0 === c9);
    ((f2 c_1 (f2 c_2 c_2)) === (f2 (f2 c_1 c_2) c_2));
    ((f2 c_2 (f2 c_0 c_2)) === (f2 (f2 c_2 c_0) c_2));
    ((f2 c_2 (f2 c_1 c_2)) === (f2 (f2 c_2 c_1) c_2));
  ] |> List.map Thm.assume in
  let goal = ((f2 c6 c8) === (f2 c7 c9)) in
  let res = CC.prove_cc_bool ctx hyps goal in
  if !debug_ then Format.printf "reg3: %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()

let reg3' _ctx =
  let module M = Make() in
  let open M in

  (* like reg3, but reverse order *)
  let hyps = [
    ((f2 c_2 (f2 c_1 c_2)) === (f2 (f2 c_2 c_1) c_2));
    ((f2 c_2 (f2 c_0 c_2)) === (f2 (f2 c_2 c_0) c_2));
    ((f2 c_1 (f2 c_2 c_2)) === (f2 (f2 c_1 c_2) c_2));
    (c_0 === c9);
    (c_2 === c8);
    (c_1 === c7);
    (c_2 === c6);
    (c_0 === (f2 c_2 c_2));
    (c_2 === (f2 c_2 c_1));
    (c_1 === (f2 c_2 c_0));
    (c_0 === (f2 c_1 c_0));
    (c_1 === (f2 c_0 c_2));
  ] |> List.map Thm.assume in
  let goal = ((f2 c6 c8) === (f2 c7 c9)) in
  let res = CC.prove_cc_bool ctx hyps goal in
  if !debug_ then Format.printf "reg3': %a@." (Fmt.Dump.option Thm.pp) res;
  assert_bool "is-res" (CCOpt.is_some res);
  ()


let suite =
  "cc" >::: [
    "reg1" >:: reg1;
    "reg2" >:: reg2;
    "reg3" >:: reg3;
    "reg3'" >:: reg3';
  ]

