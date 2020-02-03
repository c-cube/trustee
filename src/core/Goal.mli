
module Expr = Trustee_kot.Expr
module Thm = Trustee_kot.Thm
module Fmt = CCFormat

(** A goal is a sequent that we haven't proved yet. *)
type t = private {
  hyps: (string * Expr.t) list;
  concl: Expr.t;
}

val hyps : t -> (string * Expr.t) list
val concl : t -> Expr.t
val pp : t Fmt.printer

val make :
  ?hyps:(string * Expr.t) list ->
  Expr.t ->
  t
