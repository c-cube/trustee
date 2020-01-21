
(** {1 Tier-1 Rules}

    These rules are deterministic and fast, and can check basic steps with
    a minimum of proof reconstruction.
*)

type term = Core.Expr.t
type thm = Core.Thm.t

val eq_sym : term -> term -> thm 
(** [eq_sym t u] is [t=u |- u=t] *)

val eq_trans : term -> term -> term -> thm
(** [eq_trans t u v] is [t=u, u=v |- t=v] *)

val eq_proof : term list -> (term*term) -> (thm, string) result
(** [eq_proof assms (t,u)] tries to produce the theorem [asm |- t=u] *)

val eq_reflect : thm -> thm
(** [eq_reflect (F, a=a, b=b |- G)] is [F |- G].
    It removes trivial equations on the left of the sequent. *)


(* TODO: [sym a b]: [a=b |- b=a] *)
(* TODO: [trans a b c]: [a=b, b=c |- a=c], use leibniz *)

(* TODO: re-export stuff from Thm? This way it doesn't matter what is
   a primitive and what is tier-1 *)

(* TODO
val cong_t : Expr.t -> Expr.t -> Expr.t -> Expr.t -> t
(* TODO: [cong_t]: [ f=g, a=b |- f a=g b] *)
   *)
