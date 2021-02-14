
(** {1 OpenTheory parser} *)

module K = Trustee_core.Kernel

type input

module Input : sig
  type t = input

  val of_string : string -> t
  val of_chan : in_channel -> t
end

module Article : sig
  type t = {
    consts: K.Const.t list;
    axioms: K.Thm.t list;
    theorems: K.Thm.t list;
  }

  type item =
    | I_cst of K.Const.t
    | I_axiom of K.Thm.t
    | I_thm of K.Thm.t

  val items : t -> item Iter.t

  include PP with type t := t
end

val parse_and_check_art :
  K.ctx ->
  input ->
  Article.t or_error

