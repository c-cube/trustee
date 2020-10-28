
(** {1 Fixity} *)

open Sigs

type t =
  | F_normal
  | F_infix of int
  | F_left_assoc of int
  | F_right_assoc of int
  | F_prefix of int
  | F_postfix of int
  | F_binder of int

val pp : t Fmt.printer
val to_string : t -> string

val normal : t
val lassoc : int -> t
val rassoc : int -> t
val prefix : int -> t
val postfix : int -> t
val binder : int -> t
val infix : int -> t

val get_prec : t -> int

val to_string_syntax : t -> string
(** Print in a re-parsable way. *)
