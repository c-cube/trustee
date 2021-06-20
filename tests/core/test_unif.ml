
open Helpers
open OUnit2
open Trustee_core

module Make() = struct
  include Make()

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
    fun x -> app_l f [x]
  let g1 =
    let f = const c_g1 [] in
    fun x -> app_l f [x]
  let f2 =
    let f = const c_f2 [] in
    fun x y -> app_l f [x;y]
  let g2 =
    let f = const c_g2 [] in
    fun x y -> app_l f [x;y]
end

let assert_is_some msg = function
  | Some x -> x
  | None -> assert_bool msg false; assert false

let assert_eq_expr t1 t2 =
  assert_equal ~cmp:E.equal
    ~printer:(Fmt.to_string @@ Fmt.within"`" "`" E.pp) t1 t2

let reg1 ctxt =
  let module M = Make() in let open M in
  let t1 = f2 x y in
  let t2 = f2 a x in
  let subst = Unif.match_ t1 t2 |> assert_is_some "must match" in
  Format.eprintf "subst %a@." K.Subst.pp subst;
  assert_eq_expr (E.subst ~recursive:false t1 subst) t2

let suite =
  "unif" >::: [
    "reg1" >:: reg1;
  ]

