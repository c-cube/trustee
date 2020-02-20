
(** {1 Core functions to manipulate Terms and Theorems} *)

open Trustee_kot

module Fmt = CCFormat

type var = Expr.var
type term = Expr.t
type thm = Thm.t
type subst = Expr.Subst.t

(** {2 Term manipulation} *)

val unfold_lambda_exn : term -> var * term
(** [unfold_lambda_exn (λx. t)] is [(x,t)].
    @raise Error if the term is not a lambda. *)

val unfold_arrow : term -> term list * term
(** [unfold_arrow (a -> b -> c)] is [[a;b], c] *)

val free_vars : term -> Expr.Var.Set.t
(** Free variables of the term *)

val free_vars_l : term -> var list
(** Free variables of the term *)

val pi_l : var list -> term -> term
(** [pi_l [x1;…;xn] t] is [pi x1. pi x2… pi xn. t] *)

val lambda_l : var list -> term -> term
(** [lambda_l [x1;…;xn] t] is [λ x1. λ x2… λ xn. t] *)

exception Unif_fail of term * term * subst
(** Error during unification of the given
    pair of subterms, with given partial solution *)

val unify_exn : ?subst:subst -> term -> term -> subst
(** [unify_exn t1 t2] tries to unify [t1] and [t2], assuming they
    share no variables.
    @raise Unif_fail if the unification fails. *)

val unify : ?subst:subst -> term -> term -> (subst, term*term*subst) result
(** Safe version of {!unify_exn} *)

(** {2 Rules} *)

val new_poly_def : string -> term -> thm * term * var list
(** [new_poly_def c rhs] defines [c := rhs], but starts by closing [rhs]'s
    over its type variables. *)

val app1_term : term -> thm -> thm
(** [app1_term f (F |- t=u)] is [F |- (f t)=(f u)] *)

val app2_term : term -> thm -> thm
(** [app2_term x (F |- f=g)] is [F |- (f x)=(g x)] *)

(** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c].
    We reimplement it here to show it's redundant. *)
val cut' : thm -> thm -> thm

val eq_trans : term -> term -> term -> thm

val sym : thm -> thm
(** [sym (F |- t=u)] is [F |- u=t] *)

val eq_sym : term -> term -> thm
(** [eq_sym t u] is [t=u |- u=t] *)

val eq_reflect : thm -> thm
(** [eq_reflect (F, a=a, b=b |- t)] is [F |- t].
    Trivial equations in hypothesis are removed. *)

val cong_fol : term -> term list -> term list -> thm
(** [cong_fol f l1 l2] is [l1 = l2 |- f l1 = f l2] *)
