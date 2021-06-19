
(** {1 Converters} *)

open Sigs
module K = Kernel
module E = K.Expr

(** Result of a rewriting operation *)
type rw_step =
  | Same
  | Rw_step of K.thm
    (** A theorem [A |- a=b] where [a] is the initial term, and [b] the result. *)

type t = K.ctx -> K.expr -> rw_step
(** Converter: takes a term and returns a possible rewrite theorem for it *)

val empty : t
(** Converter that does nothing *)

val fix : t -> t
(** Apply converter repeatedly. *)

val combine : t -> t -> t
(** [combine c1 c2] tries to normalize a term using [c1];
    if [c1] fails it tries [c2]. *)

val combine_l : t list -> t
(** N-ary version of {!combine} *)
