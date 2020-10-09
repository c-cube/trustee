
open Sigs

module K = Kernel
module P = Parser_comb

module Ast : sig
  type t
  type ty

  val pos : t -> Position.t
  val ty_pos : ty -> Position.t

  val pp_ty : ty Fmt.printer
  val pp : t Fmt.printer
end

val ty : Ast.ty P.t
val expr : K.Ctx.t -> Ast.t P.t

val ty_eof : Ast.ty P.t
val expr_eof : K.Ctx.t -> Ast.t P.t
