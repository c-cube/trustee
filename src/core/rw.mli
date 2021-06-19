
(** {1 Rewriting}

    This module contains rewriting structures and algorithms that use
    the {!Conv} interface. *)

open Sigs
module K = Kernel

type conv = Conv.t

(** {2 Rewriting terms} *)

val bottom_up : conv -> conv
(** Bottom-up rewriting.
    The [conv] is called on every subterm, starting from the leaves. *)

(** {2 Rewriting} *)

(** Rewrite rule *)
module Rule : sig
  type t
  (** A rewrite rule, with a LHS (left-hand side) pattern
      and some way of computing the RHS (right-hand side) from it when
      it matches a term. *)

  val pp : t Fmt.printer

  val to_conv : t -> conv
  (** Make a converter from a single rule *)

  val mk_rule :
    K.expr ->
    K.thm ->
    t
  (** A rewrite rule, i.e. an equation.
      The theorem should be [|- lhs = rhs]
      to rewrite instances of [lhs] into instances of [rhs].
  *)

  val mk_dynamic :
    K.expr ->
    (K.ctx -> K.expr -> K.Subst.t -> K.thm option) ->
    t
  (** [mk_dynamic lhs f] can generate a rule [|- subst(lhs) = rhs]
      on the fly, or [None] *)

  (* TODO: an instance of mk_dynamic that uses a term ordering *)
end

(** A set of rewrite rules *)
module RuleSet : sig
  type t

  val empty : t
  val size : t -> int

  val of_list : Rule.t list -> t
  val to_iter : t -> Rule.t Iter.t

  val to_conv : t -> conv
  (** Converter that tries each rule in the rule set.
      The implementation might be more efficient that trying each rule
      one by one, so the order in which rules are tried is {b not} specified. *)
end

(** {2 Rewriting module Associativity and Commutativity} *)

(** AC rewrite rules *)
module AC_rule : sig
  (** AC-rewrite rule for one symbol. *)
  type t

  val make :
    f:K.expr ->
    assoc:K.thm ->
    comm:K.thm ->
    unit -> t

  val pp : t Fmt.printer

  val to_conv : t -> conv
  (** Converter that applies AC-rewriting. *)
end
