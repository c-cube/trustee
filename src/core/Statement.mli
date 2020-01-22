module Expr = Kernel_of_trust.Expr
module Thm = Kernel_of_trust.Thm
module Fmt = CCFormat

type t =
  | St_decl of Expr.t
  | St_prove of Goal.t

(* TODO: statements for:
   - show current goal
   - show a symbol's type
   - include (read a file)
   - apply tactic to current goal?
*)

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
