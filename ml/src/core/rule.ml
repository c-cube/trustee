
open Sigs
module K = Kernel

type arg =
  | Arg_expr
  | Arg_thm
  | Arg_subst

type signature = arg list

type t = {
  r_name: string;
  r_args: arg list;
  r_view: view;
}

and view =
  | R_assume
  | R_axiom
  | R_cut
  | R_refl
  | R_congr
  | R_congr_ty
  | R_subst
  | R_sym
  | R_bool_eq
  | R_bool_eq_intro
  | R_beta_conv
  | R_defined of defined_rule

and defined_rule = unit (* TODO *)
(** A defined rule *)

let mk_ r_name r_view r_args : t =
  { r_name; r_view; r_args; }

let assume : t = mk_ "assume" R_assume [Arg_expr]
let axiom : t = mk_ "axiom" R_axiom [Arg_expr]
let cut : t = mk_ "cut" R_cut [Arg_thm; Arg_thm]
let refl : t = mk_ "refl" R_refl [Arg_expr]
let congr : t = mk_ "congr" R_congr [Arg_thm; Arg_thm]
let congr_ty : t = mk_ "congr_ty" R_congr_ty [Arg_thm; Arg_thm]
let subst : t = mk_ "subst " R_subst [Arg_subst; Arg_thm]
let sym : t = mk_ "sym" R_sym [Arg_thm]
let bool_eq : t = mk_ "bool_eq" R_bool_eq [Arg_thm; Arg_thm]
let bool_eq_intro : t = mk_ "bool_eq_intro" R_bool_eq_intro [Arg_thm; Arg_thm]
let beta_conv : t = mk_ "beta_conv" R_beta_conv [Arg_expr]

let builtins : t list = [
  assume; axiom; cut; refl; congr; sym; congr_ty; subst;
  bool_eq; bool_eq_intro; beta_conv;
]
let find_builtin s =
  try Some (List.find (fun r -> String.equal r.r_name s) builtins)
  with Not_found -> None

let signature r = r.r_args

let pp out (r:t) : unit = Fmt.string out r.r_name
let to_string = Fmt.to_string pp

let string_of_arg = function
  | Arg_thm -> "thm"
  | Arg_subst -> "subst"
  | Arg_expr -> "expr"
let pp_arg out a = Fmt.string out (string_of_arg a)
let pp_signature = Fmt.Dump.list pp_arg

(* TODO
val apply : K.Ctx.t -> t -> exprs:K.Expr.t list -> thm:K.Thm
   *)

module Defined_rule = struct
  type nonrec t = t

  (* TODO: definition of the body.
  type register = int (** A virtual register *)

  type instr = {
    ret: register;
    op: instr_op;
  }
  and instr_op =
    | I_subst of register * register
    | I_apply of register * t * register list
  type body = instr_op list

  val mk_defined :
    name:string ->
    args:arg list ->
    body:instr list ->
    unit -> t
  *)
end
