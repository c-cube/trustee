
open Trustee_kot

val true_ : Expr.t
val false_ : Expr.t

val true_def : Thm.t
val false_def : Thm.t

val true_is_true : Thm.t
(** [|- true] *)

val true_eq_intro : Thm.t -> Thm.t
(** [true_eq_elim (F |- t)] is [F |- t=true] *)

val true_eq_elim : Thm.t -> Thm.t
(** [true_eq_elim (F |- t=true)] is [F |- t] *)

val and_const : Expr.t
val or_const : Expr.t
val not_const : Expr.t

val and_ : Expr.t -> Expr.t -> Expr.t
val or_ : Expr.t -> Expr.t -> Expr.t
val and_l : Expr.t list -> Expr.t
val or_l : Expr.t list -> Expr.t
val not_ : Expr.t -> Expr.t

