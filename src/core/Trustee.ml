
(** {1 Trustee: A multi-tiered proof checker}

    The project relies on a LCF-style kernel of trust (in {!Core}),
    which contains all the axioms. We refer to these axioms (or axiom schemes)
    as "tier-0 rules", and to theorems obtained directly
    from {!Core.Thm} as "tier-0 theorems".

    (TODO)
    A collection of basic proof checkers built on top of {!Core.Thm},
    intended to be deterministic, predictible, and fast, constitute
    the "tier-1 rules" that produce "tier-1 theorems".

    (TODO)
    A collection of more advanced proof reconstruction techniques, which produce
    {b proof traces} where each step is of tier 0 or 1, are called the "tier-2"
    rules.
    A FO/HO theorem prover may be able to output proof traces where each
    step is annotated with a tier-1 or tier-2 rule. Trustee can then be
    used to check these proofs (and optionally produce a tier-1 proof
    that can be efficiently re-checked later).
*)

module Kernel = Trustee_kernel

module Make(K : Trustee_kernel.S) = struct
  module K = K
  module ID = K.ID
  module Expr = K.Expr
  module Thm = K.Thm

  module Core = Core.Make(K)
  module Bool = Bool.Make(Core)
  module Goal = Goal.Make(Core)
  module Tactic = Tactic.Make(Core)
  module Statement = Statement.Make(Core)
  module Open_theory = Open_theory.Make(Core)
end
