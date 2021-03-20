
(** {1 Rewriting} *)

open Sigs
module K = Kernel

(** Result of a rewriting operation *)
type rw_result =
  | Same
  | Rw_step of K.thm
    (** A theorem [A |- a=b] where [a] is the initial term, and [b] the result. *)

type conv = K.ctx -> K.expr -> rw_result
(** Converter: takes a term and returns a possible rewrite theorem for it *)

val bottom_up : K.ctx -> conv -> K.expr -> rw_result
(** Bottom-up rewriting.
    The [conv] is called on every subterm, starting from the leaves. *)

(** {2 Rewrite rules} *)
module Rule : sig
  type t = {
    lhs: K.expr;
    th: K.thm; (* lhs = rhs *)
  }
  (** A rewrite rule, i.e. an equation *)

  val pp : t Fmt.printer
  val to_conv : t -> conv
end

(** {2 A set of rewrite rules} *)
module RuleSet : sig
  type t

  val empty : t
  val size : t -> int

  val of_list : Rule.t list -> t
  val to_iter : t -> Rule.t Iter.t

  val to_conv : t -> conv
end
