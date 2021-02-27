
module K = Trustee_core.Kernel
module E = K.Expr

open OUnit2

module Make() = struct
  module E = K.Expr
  module Subst = K.Subst
  module Thm = K.Thm
  let ctx = K.Ctx.create ()
  let bool = K.Expr.bool ctx
  let c_bool = K.Const.bool ctx
  let type_ = K.Expr.type_ ctx
  let tau = K.Expr.const ctx (K.Expr.new_ty_const ctx "tau" 0) []
  let lambda v t = K.Expr.lambda ctx v t
  let v' s ty = K.Var.make s ty
  let v x = K.Expr.var ctx x
  let (@->) a b = K.Expr.arrow ctx a b
  let (@@) a b = K.Expr.app ctx a b
  let new_const s ty = K.Expr.new_const ctx s [] ty
  let const c = K.Expr.const ctx c []
  let a = new_const "a0" tau
  let b = new_const "b0" tau
  let c = new_const "c0" tau
  let f1 = new_const "f1" (tau @-> tau)
  let g1 = new_const "g1" (tau @-> tau)
  let h1 = new_const "h1" (tau @-> tau)
  let f2 = new_const "f2" (tau @-> tau @-> tau)
  let g2 = new_const "g2" (tau @-> tau @-> tau)
  let h2 = new_const "h2" (tau @-> tau @-> tau)
  let p0 = new_const "p0" bool
  let q0 = new_const "q0" bool
  let r0 = new_const "r0" bool
  let p1 = new_const "p1" (tau @-> bool)
  let q1 = new_const "q1" (tau @-> bool)
  let r1 = new_const "r1" (tau @-> bool)
  let p2 = new_const "p2" (tau @-> tau @-> bool)
  let q2 = new_const "q2" (tau @-> tau @-> bool)
  let r2 = new_const "r2" (tau @-> tau @-> bool)
  let forall = new_const "!" ((tau @-> bool) @-> bool)
  let () = K.Const.set_fixity forall (F_binder 10)
  let c_plus = new_const "+" (tau @-> tau @-> tau)
  let plus a b = K.Expr.app_l ctx (K.Expr.const ctx c_plus []) [a;b]
  let c_eq = K.Const.eq ctx
  let (=) = K.Expr.app_eq ctx
  let () = K.Const.set_fixity c_plus (F_right_assoc 20)
end

(* test substitution of terms and types *)
let t_subst1 _ctx =
  let module M = Make() in
  let open M in
  let a' = v' "a" type_ in
  let x = v' "x" (v a') in
  let c_foo = new_const "foo" tau in
  let foo = const c_foo in
  let th =
    Thm.axiom ctx (v x = (lambda x (v x) @@ v x))
  in
  let x_tau = v' "x" tau in
  let subst =
    Subst.of_list [a', tau; x_tau, foo]
  in
  let th' = Thm.subst ~recursive:false ctx th subst in
  assert_equal ~cmp:E.equal ~printer:E.to_string
    (foo = lambda x_tau (v x_tau) @@ foo)
    (Thm.concl th');
  ()


let suite =
  "kernel" >::: [
    "t_subst11" >:: t_subst1;
  ]

