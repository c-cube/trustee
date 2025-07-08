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
  let v_x = K.Var.make "x" tau
  let v_y = K.Var.make "y" tau
  let v_z = K.Var.make "z" tau
  let x = var v_x
  let y = var v_y
  let z = var v_z
  let x1 = var_name "x1" tau
  let y1 = var_name "y1" tau

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

  let ax_f2_assoc = Thm.axiom ctx [] (f2 (f2 x y) z === f2 x (f2 y z))
  let ax_f2_comm = Thm.axiom ctx [] (f2 x y === f2 y x)
  let ax_g2_assoc = Thm.axiom ctx [] (g2 (g2 x y) z === g2 x (g2 y z))
  let ax_g2_comm = Thm.axiom ctx [] (g2 x y === g2 y x)
  let ax_g2_idem = Thm.axiom ctx [] (g2 x x === x)

  let rules_ac =
    Conv.combine_l
      [
        Rw.AC_rule.make ctx ~f:(const c_f2 []) ~assoc:ax_f2_assoc
          ~comm:ax_f2_comm ()
        |> Rw.AC_rule.to_conv;
        Rw.AC_rule.make ctx ~f:(const c_g2 []) ~assoc:ax_g2_assoc
          ~comm:ax_g2_comm ()
        |> Rw.AC_rule.to_conv;
      ]

  (* AC + idempotence of g2 *)
  let rules_aci =
    Conv.combine rules_ac (Rw.Rule.mk_rule ax_g2_idem |> Rw.Rule.to_conv)

  let assert_rw_eq conv t1 t2 =
    let u1, _ = Conv.apply_e (Rw.bottom_up conv) ctx t1 in
    let u2, _ = Conv.apply_e (Rw.bottom_up conv) ctx t2 in
    if not (E.equal u1 u2) then
      assert_bool
        (Fmt.asprintf
           "@[<v>terms do not rewrite to same term:@ `%a` --> `%a`@ but `%a` \
            --> `%a`@]"
           E.pp t1 E.pp u1 E.pp t2 E.pp u2)
        false

  let assert_e_eq t1 t2 = assert_equal ~cmp:E.equal ~printer:E.to_string t1 t2

  (* generates terms of type [tau] *)
  let gen_e : E.t QCheck.Gen.t =
    let open QCheck.Gen in
    let gen_rec self depth =
      let atom_cases =
        [
          1, return a;
          1, return b;
          1, return c;
          1, return x;
          1, return y;
          1, return z;
          1, return x1;
          1, return y1;
        ]
      in
      if depth = 0 then
        frequency atom_cases
      else
        frequency
          (atom_cases
          @ [
              ( 2,
                let+ x = self (depth - 1) in
                f1 x );
              ( 2,
                let+ x = self (depth - 1) in
                g1 x );
              ( 1,
                let+ x = self (depth - 1) and+ y = self (depth - 1) in
                f2 x y );
              ( 1,
                let+ x = self (depth - 1) and+ y = self (depth - 1) in
                g2 x y );
              ( 1,
                let+ x = oneofl [ v_x; v_y; v_z ]
                and+ bod = self (depth - 1)
                and+ u = self (depth - 1) in
                app (lambda x bod) u );
            ])
    in
    sized_size (0 -- 7) (fix gen_rec)

  let shrink_e e =
    let open QCheck in
    (* shrink to a subterm with the same type *)
    fun yield ->
      E.iter_dag e ~iter_ty:false ~f:(fun u ->
          if e != u && E.is_closed u && E.ty_exn e == E.ty_exn u then yield y)

  let arb_e = QCheck.make ~print:E.to_string ~shrink:shrink_e gen_e
end

let test1 _ctx =
  let module M = Make () in
  let open M in
  let t1 = f2 (f2 (f2 a b) b) (g1 a) in
  let t2 = f2 (g1 a) (f2 b (f2 b a)) in
  assert_rw_eq rules_ac t1 t2

let test2 _ctx =
  let module M = Make () in
  let open M in
  let t1 = g2 (g2 (g2 a b) b) (g1 a) in
  let t2 = g2 (g1 a) (g2 b a) in
  assert_rw_eq rules_aci t1 t2

let t_rw_idempotent1 : test =
  let module M = Make () in
  let open M in
  QCheck_ounit.to_ounit2_test ?rand:None
  @@ QCheck.Test.make ~name:"rw_idempotent1" arb_e
  @@ fun e ->
  let rhs, _ = Conv.apply_e rules_ac ctx e in
  let rh2, _ = Conv.apply_e rules_ac ctx rhs in
  assert_e_eq rhs rh2;
  true

let t_rw_idempotent2 : test =
  let module M = Make () in
  let open M in
  QCheck_ounit.to_ounit2_test ?rand:None
  @@ QCheck.Test.make ~name:"rw_idempotent2" arb_e
  @@ fun e ->
  let rhs, _ = Conv.apply_e rules_aci ctx e in
  let rh2, _ = Conv.apply_e rules_aci ctx rhs in
  assert_e_eq rhs rh2;
  true

(*
   TODO: test AC normalization (use and/or with AC axioms + idempotence
   and see if we can convert formulas into one another)
   *)

let suite =
  "rw"
  >::: [
         "test1" >:: test1;
         "test2" >:: test2;
         t_rw_idempotent1;
         t_rw_idempotent2;
       ]
