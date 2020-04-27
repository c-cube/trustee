
module Fmt = CCFormat

module Make(C : Core.S) : sig
  open C.KoT
  module Goal : module type of struct include Goal.Make(C) end
  module OT : module type of Open_theory.Make(C)

  type t =
    | St_decl of Expr.t
    | St_prove of Goal.t
    | St_load_opentheory of string

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

    val defs : ctx -> OT.Defs.t
    val decl : ctx -> string -> ty:Expr.t -> Expr.t
    val find : ctx -> string -> Expr.t option
    val find_exn : ctx -> string -> Expr.t
    val decl_local : ctx -> string -> ty:Expr.t -> Expr.var * (unit->unit)
  end
end