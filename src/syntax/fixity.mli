(** Fixity

    Symbols can be infix, prefix, misfix, etc. with various precedence. A high
    precedence means the symbol binds more tightly, which means it takes
    precedence(!) over other binders or infix symbols.

    For example "×" has a higher precedence than "+" in classic math notation.
*)

type precedence = int

type t =
  | F_normal
  | F_infix of precedence
  | F_left_assoc of precedence
  | F_right_assoc of precedence
  | F_prefix of precedence
  | F_postfix of precedence
  | F_binder of precedence

val pp : t Fmt.printer
val to_string : t -> string
val normal : t
val lassoc : precedence -> t
val rassoc : precedence -> t
val prefix : precedence -> t
val postfix : precedence -> t
val binder : precedence -> t
val infix : precedence -> t
val get_prec : t -> precedence
val pp_syntax : t Fmt.printer

val to_string_syntax : t -> string
(** Print in a re-parsable way. *)
