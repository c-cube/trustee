
module Fmt = CCFormat
module K = Trustee_core.Kernel
module E = K.Expr

module Make() = struct
  let ctx = K.Ctx.create ()
  module E = (val K.make_expr ctx)
  module Subst = K.Subst
  module Thm = (val K.make_thm ctx)

  include E
  let c_bool = K.Const.bool ctx
  let tau = E.const (E.new_ty_const "tau" 0) []
  let v' s ty = K.Var.make s ty
  let v = E.var
  let (@->) = E.arrow
  let (@@) = E.app
  let new_const s ty = E.new_const s [] ty
  let const' c = E.const c []
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
  (*   let () = K.Const.set_fixity forall (F_binder 10) *)
  let c_plus = new_const "+" (tau @-> tau @-> tau)
  let plus a b = app_l (const' c_plus) [a;b]
  let c_eq = K.Const.eq ctx
  let (=) = E.app_eq
  (*   let () = K.Const.set_fixity c_plus (F_right_assoc 20) *)
end
