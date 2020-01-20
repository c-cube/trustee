
(** {1 Tier-1 Rules}

    These rules are deterministic and fast, and can check basic steps with
    a minimum of proof reconstruction.
*)

type term = Core.Expr.t
type thm = Core.Thm.t

val eq_proof : term list -> (term*term) -> (thm, string) result
(** [eq_proof assms (t,u)] tries to produce the theorem [asm |- t=u] *)
