
(** {1 KBO term ordering} *)

module K = Kernel

type result =
  | Gt
  | Lt
  | Eq
  | Incomparable

type params = {
  var_as_cst: bool;
  (** if true, variables are just considered to be
      constants and are totally ordered in an unspecified but stable way.
      If false, then variables are incomparable and [a > b] implies that
      the multiset of variables of [a] contains the one of [b]. *)

  precedence: Name.t -> Name.t -> int;
  (** Total order on constants *)

  weight : Name.t -> int;
  (** Weight of constants. Must always be [>= 1]
      (we ignore the edge cases where one unary symbol can have weight 0
      for simplicity) *)
}

val compare : ?params:params -> K.expr -> K.expr -> result
(** Compare the two terms. *)

val lt : ?params:params -> K.expr -> K.expr -> bool
     (** [lt a b] is true iff [compare a b = Lt].
     See {!compare} for more details *)

val gt : ?params:params -> K.expr -> K.expr -> bool


