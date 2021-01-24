
open Sigs
module K = Kernel

module Rule : sig
  type arg_ty =
    | Arg_expr
    | Arg_thm
    | Arg_subst

  type arg_val =
    | AV_expr of K.Expr.t
    | AV_thm of K.Thm.t
    | AV_subst of K.Subst.t

  type signature = arg_ty list

  type t

  val assume : t
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
  val pp_arg_ty : arg_ty Fmt.printer
  val pp_arg_val : arg_val Fmt.printer
  val pp_signature : signature Fmt.printer

  val signature : t -> signature

  val builtins : t list
  val find_builtin : string -> t option

  val apply : K.Ctx.t -> t -> arg_val list -> K.Thm.t

  (* TODO: defined rules *)
end

module Defined_rule : sig
  type t = Rule.t

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

