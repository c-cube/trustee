
(** {1 Tier-1 Rules}

    These rules are deterministic and fast, and can check basic steps with
    a minimum of proof reconstruction.
*)

type term = Core.Expr.t
type thm = Core.Thm.t

val eq_proof : term list -> (term*term) -> (thm, string) result
(** [eq_proof assms (t,u)] tries to produce the theorem [asm |- t=u] *)


(* TODO: [sym a b]: [a=b |- b=a] *)
(* TODO: [trans a b c]: [a=b, b=c |- a=c], use leibniz *)

(* TODO: re-export stuff from Thm? This way it doesn't matter what is
   a primitive and what is tier-1 *)
