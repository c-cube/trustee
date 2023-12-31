(** {1 Congruence closure} *)

module K = Kernel

val prove_cc_eqn : K.ctx -> K.thm list -> K.expr -> K.expr -> K.thm option
(** [prove_cc_eqn ctx hyps t u] tries to prove [hyps |- t = u] by congruence closure.
    If it succeeds it returns [Some (\Gamma |- t=u)] where [\Gamma]
    is a subset of [hyps]. *)

val prove_cc_bool : K.ctx -> K.thm list -> K.expr -> K.thm option
(** [prove_cc_bool ctx hyps res] tries to prove the boolean [res]
    from the hypotheses [hyps], that is, [hyps |- res].
    If [res] is an equation, [prove_cc_bool] behaves like
    [prove_cc_eqn]; otherwise it needs an hypothesis to be [p]
    and the conclusion to be [p'], where [hyps \ {p} |- p=p'].
*)

val prove_cc_false :
  K.ctx ->
  prove_false:(K.ctx -> K.thm -> K.thm -> K.thm) ->
  not_e:K.expr ->
  K.thm list ->
  K.thm option
(** [prove_cc_false ctx ~prove_false ~not_e hyps]
    tries to prove [false] from the theorems in [hyps].
    @param prove_false a function such that [prove_false ctx (|- a) (|- ¬ a)]
    returns [|- false]
    @param not_e the constant [¬]
*)
