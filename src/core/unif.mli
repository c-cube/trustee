
(** {1 Unification of Kernel terms} *)

module K = Kernel

type subst = K.Subst.t

exception Fail

val unify_exn : ?subst:subst -> K.expr -> K.expr -> subst

val unify : ?subst:subst -> K.expr -> K.expr -> subst option

val match_exn : ?subst:subst -> K.expr -> K.expr -> subst

val match_ : ?subst:subst -> K.expr -> K.expr -> subst option
