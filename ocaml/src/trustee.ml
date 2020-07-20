
type expr
type ty = expr
type thm
type ctx

module Expr = struct
  type t = expr
  external to_string : t -> string = "trustee_expr_to_string"
  external is_type : t -> bool = "trustee_expr_is_type"
  external ty : t -> t = "trustee_expr_ty"
  let pp out e = Format.fprintf out "@[%a@]" Format.pp_print_text (to_string e)
end

module Thm = struct
  type t = thm
  external to_string : t -> string = "trustee_thm_to_string"
  external concl : t -> expr = "trustee_thm_concl"
  external hyps : t -> expr array = "trustee_thm_hyps"
  let hyps_l th = Array.to_list (hyps th)
  let pp out self =
    Format.fprintf out "@[%a@]" Format.pp_print_text (to_string self)
end

module Ctx = struct
  type t = ctx
  external create : unit -> t = "trustee_new_ctx"
  external parse_ot_str : t -> string -> expr list * thm list * thm list = "trustee_ot_parse"
  let parse_ot_file vm f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let content = really_input_string ic n in
    parse_ot_str vm content
end

module OpenTheory = struct
  type vm
(*   external create : ctx -> vm = "trustee_ot_create" *)
  external parse_ot_str : ctx -> string -> (expr list * thm list * thm list) = "trustee_ot_parse"
  let _read_file f : string =
    let ic = open_in f in
    let n = in_channel_length ic in
    really_input_string ic n
  let parse_ot_files ctx fs =
    let s = String.concat "\n" (List.map _read_file fs) in
    parse_ot_str ctx s
  let parse_ot_file ctx f =
    parse_ot_str ctx (_read_file f)
      (*
  external defs : vm -> expr array = "trustee_ot_defs"
  external axioms : vm -> thm array = "trustee_ot_axioms"
  external theorems : vm -> thm array = "trustee_ot_theorems"
       *)
end

external mk_type : ctx -> ty = "trustee_mk_type"
external mk_bool : ctx -> ty = "trustee_mk_bool"
external mk_var : ctx -> string -> ty -> expr = "trustee_mk_var"
external mk_app : ctx -> expr -> expr -> expr = "trustee_mk_app"
external mk_arrow : ctx -> expr -> expr -> expr = "trustee_mk_arrow"
external mk_eq : ctx -> expr -> expr -> expr = "trustee_mk_eq_app"

external assume : ctx -> expr -> thm = "trustee_thm_assume"
