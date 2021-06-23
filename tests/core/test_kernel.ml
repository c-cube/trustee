
open Helpers
open OUnit2

(* test substitution of terms and types *)
let t_subst1 _ctx =
  let module M = Make() in
  let open M in
  let a' = v' "a" type_ in
  let x = v' "x" (v a') in
  let c_foo = new_const "foo" tau in
  let foo = const c_foo [] in
  let th =
    Thm.axiom [] (v x === (lambda x (v x) @@@ v x))
  in
  let x_tau = v' "x" tau in
  let subst =
    Subst.of_list [a', tau; x_tau, foo]
  in
  let th' = Thm.subst ~recursive:false th subst in
  assert_equal ~cmp:E.equal ~printer:E.to_string
    (foo === lambda x_tau (v x_tau) @@@ foo)
    (Thm.concl th');
  ()


let suite =
  "kernel" >::: [
    "t_subst11" >:: t_subst1;
  ]

