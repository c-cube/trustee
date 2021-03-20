

(** {1 Congruence closure} *)

module K = Kernel

val prove_cc : K.ctx -> K.thm list -> K.expr -> K.expr -> K.thm option
(** [prove_cc ctx hyps t u] tries to prove [hyps |- t = u] by congruence closure.
    If it succeeds it returns [Some (\Gamma |- t=u)] where [\Gamma]
    is a subset of [hyps]. *)




