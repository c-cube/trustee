
open Sigs
module K = Kernel

type arg =
  | Arg_expr
  | Arg_thm
  | Arg_subst

type t = private {
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

and defined_rule
(** A defined rule *)

val assume : t
val axiom : t
val cut : t
val refl : t
val congr : t
val congr_ty : t
val subst : t
val sym : t
val bool_eq : t
val bool_eq_intro : t
val beta_conv : t

include PP with type t := t

val builtins : t list
val builtin_of_string : string -> t option

(* TODO: bridge to context methods
val apply : K.Ctx.t -> t -> exprs:K.Expr.t list -> thm:K.Thm
   *)

module Defined_rule : sig
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

