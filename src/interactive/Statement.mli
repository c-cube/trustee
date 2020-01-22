open Trustee
module Fmt = CCFormat

type t =
  | St_decl of Expr.t
  | St_prove of Goal.t

val pp : t Fmt.printer

type ctx
module Ctx : sig
  type t = ctx
  val create : unit -> ctx

  val decl : ctx -> string -> ty:Expr.t -> Expr.t
  val find : ctx -> string -> Expr.t option
  val find_exn : ctx -> string -> Expr.t
  val decl_local : ctx -> string -> ty:Expr.t -> Expr.var * (unit->unit)
end
