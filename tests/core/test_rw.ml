
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
  let z = var_name "z" tau
  let x1 = var_name "x1" tau
  let y1 = var_name "y1" tau

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

  let ax_f2_assoc = Thm.axiom [] (f2 (f2 x y) z === f2 x (f2 y z))
  let ax_f2_comm = Thm.axiom [] (f2 x y === f2 y x)

  let ax_g2_assoc = Thm.axiom [] (g2 (g2 x y) z === g2 x (g2 y z))
  let ax_g2_comm = Thm.axiom [] (g2 x y === g2 y x)

  let ax_g2_idem = Thm.axiom [] (g2 x x === x)

  let rules_ac =
    Conv.combine_l [
      Rw.AC_rule.make ctx ~f:(const c_f2 []) ~assoc:ax_f2_assoc ~comm:ax_f2_comm () |> Rw.AC_rule.to_conv;
      Rw.AC_rule.make ctx ~f:(const c_g2 []) ~assoc:ax_g2_assoc ~comm:ax_g2_comm () |> Rw.AC_rule.to_conv;
    ]

  let rules_aci =
    Conv.combine rules_ac (Rw.Rule.mk_rule ax_g2_idem |> Rw.Rule.to_conv)

  let assert_rw_eq conv t1 t2 =
    let u1, _ = Conv.apply_e (Rw.bottom_up conv) ctx t1 in
    let u2, _ = Conv.apply_e (Rw.bottom_up conv) ctx t2 in
    if not (E.equal u1 u2) then (
      assert_bool
        (Fmt.asprintf "@[<v>terms do not rewrite to same term:@ `%a` --> `%a`@ but `%a` --> `%a`@]"
           E.pp t1 E.pp u1 E.pp t2 E.pp u2)
        false

    )
end

let test1 _ctx =
  let module M = Make() in let open M in
  let t1 = f2 (f2 (f2 a b) b) (g1 a) in
  let t2 = f2 (g1 a) (f2 b (f2 b a)) in
  assert_rw_eq rules_ac t1 t2

let test2 _ctx =
  let module M = Make() in let open M in
  let t1 = g2 (g2 (g2 a b) b) (g1 a) in
  let t2 = g2 (g1 a) (g2 b a) in
  assert_rw_eq rules_aci t1 t2

(*
   TODO: test AC normalization (use and/or with AC axioms + idempotence
   and see if we can convert formulas into one another)
   *)

let suite =
  "rw" >::: [
    "test1" >:: test1;
    "test2" >:: test2;
  ]

