
open Trustee_kot

val and_const : Expr.t
val or_const : Expr.t
val not_const : Expr.t

val and_ : Expr.t -> Expr.t -> Expr.t
val or_ : Expr.t -> Expr.t -> Expr.t
val and_l : Expr.t list -> Expr.t
val or_l : Expr.t list -> Expr.t
val not_ : Expr.t -> Expr.t

