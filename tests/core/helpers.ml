module Fmt = CCFormat
module K = Trustee_core.Kernel
module E = K.Expr

module Make () = struct
  let ctx = K.Ctx.create ()

  module E = K.Expr
  module Subst = K.Subst
  module Thm = K.Thm
  include E

  let c_bool = K.Const.bool ctx
  let tau = E.const ctx (K.Ctx.new_skolem_ty_const ctx "tau" ~arity:0) []
  let v' s ty = K.Var.make s ty
  let bool = E.bool ctx
  let type_ = E.type_ ctx
  let v = E.var ctx
  let app_eq = E.app_eq ctx
  let ( @-> ) = E.arrow ctx
  let ( @@@ ) = E.app ctx
  let new_const s ty = K.Ctx.new_skolem_const ctx s [] ty
  let const' c = E.const ctx c []
  let const c l = E.const ctx c l
  let var_name = E.var_name ctx
  let var = E.var ctx
  let app = E.app ctx
  let lambda = E.lambda ctx
  let app_l = E.app_l ctx
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
  let plus a b = app_l (const' c_plus) [ a; b ]
  let c_eq = K.Const.eq ctx
  let ( === ) = app_eq
  (*   let () = K.Const.set_fixity c_plus (F_right_assoc 20) *)
end
