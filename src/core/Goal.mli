
module Expr = Kernel_of_trust.Expr
module Thm = Kernel_of_trust.Thm
module Fmt = CCFormat

(** A goal is a sequent that we haven't proved yet. *)
type t = private {
  hyps: (string * Thm.t) list;
  concl: Expr.t;
}

val hyps : t -> (string * Thm.t) list
val concl : t -> Expr.t
val pp : t Fmt.printer

val make :
  ?hyps:(string * Thm.t) list ->
  Expr.t ->
  t
