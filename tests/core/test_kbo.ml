open Helpers
open OUnit2
open Trustee_core

module Make () = struct
  include Make ()

  let a = const a []

  let b = const b []

  let c = const c []

  let c_f1 = new_const "f1" (tau @-> tau)

  let c_g1 = new_const "g1" (tau @-> tau)

  let c_f2 = new_const "f2" (tau @-> tau @-> tau)

  let c_g2 = new_const "g2" (tau @-> tau @-> tau)

  let x = var_name "x" tau

  let y = var_name "y" tau

  let f1 =
    let f = const c_f1 [] in
    fun x -> app_l f [ x ]

  let g1 =
    let f = const c_g1 [] in
    fun x -> app_l f [ x ]

  let f2 =
    let f = const c_f2 [] in
    fun x y -> app_l f [ x; y ]

  let g2 =
    let f = const c_g2 [] in
    fun x y -> app_l f [ x; y ]
end

let str_cmp = function
  | KBO.Lt -> "lt"
  | KBO.Gt -> "gt"
  | KBO.Eq -> "eq"
  | KBO.Incomparable -> "incomparable"

let assert_cmp_ exp t1 t2 =
  assert_equal ~printer:str_cmp exp (KBO.compare t1 t2);
  ()

let t1 _ctx =
  let module M = Make () in
  let open M in
  assert_cmp_ Lt (f2 (f1 a) (g1 b)) (f2 (f1 a) (g1 (g1 b)))

let t2 _ctx =
  let module M = Make () in
  let open M in
  assert_cmp_ Eq (f2 (f1 a) (g1 b)) (f2 (f1 a) (g1 b))

let t3 _ctx =
  let module M = Make () in
  let open M in
  assert_cmp_ Incomparable (f2 (f1 x) (g1 b)) (f2 (f1 a) (g1 y))

let t4 _ctx =
  let module M = Make () in
  let open M in
  assert_cmp_ Gt (f2 (f1 b) (g2 x b)) (f2 (f1 a) (g2 b x))

(*
   TODO: qcheck (subterm; substitution stability; a>b => b<a)
   *)

let suite = "kbo" >::: [ "t1" >:: t1; "t2" >:: t2; "t3" >:: t3; "t4" >:: t4 ]
