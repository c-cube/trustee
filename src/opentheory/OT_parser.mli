
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

  val empty : t
  include PP with type t := t

  type item =
    | I_cst of K.Const.t
    | I_axiom of K.Thm.t
    | I_thm of K.Thm.t

  val items : t -> item Iter.t
end

(** {2 Virtual Machine} *)
module VM : sig
  type t

  val create : K.ctx -> t

  include PP with type t := t

  val article : t -> Article.t
  val clear_article : t -> unit

  val clear_dict : t -> unit

  val has_empty_stack : t -> bool

  val parse_and_check_art :
    t ->
    input ->
    Article.t or_error
end

val parse_and_check_art :
  K.ctx ->
  input ->
  Article.t or_error

