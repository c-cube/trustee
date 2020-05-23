
type expr
type ty = expr

module Expr = struct
  type t = expr
  external to_string : t -> string = "trustee_expr_to_string"
  external is_type : t -> bool = "trustee_expr_is_type"
  external ty : t -> t = "trustee_expr_ty"
  let pp out e = Format.pp_print_string out (to_string e)
end

type ctx

module Ctx = struct
  type t = ctx
  external create : unit -> t = "trustee_new_ctx"
end

external mk_type : ctx -> ty = "trustee_mk_type"
external mk_bool : ctx -> ty = "trustee_mk_bool"
external mk_var : ctx -> string -> ty -> expr = "trustee_mk_var"
external mk_app : ctx -> expr -> expr -> expr = "trustee_mk_app"
external mk_arrow : ctx -> expr -> expr -> expr = "trustee_mk_arrow"
external mk_eq : ctx -> expr -> expr -> expr = "trustee_mk_eq_app"
