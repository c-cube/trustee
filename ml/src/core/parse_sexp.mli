
module K = Kernel

module Sexp : sig
  type t
  include CCSexp_intf.S with type t := t
end

val parse_sexps :
  K.Ctx.t ->
  on_expr:(K.Expr.t -> unit) ->
  on_thm:(K.Thm.t -> unit) ->
  Sexp.t list ->
  unit


