
module Expr = Trustee_kot.Expr
module Thm = Trustee_kot.Thm

type goal = Goal.t
type subgoals = goal list * (Thm.t list -> Thm.t)

type t = goal -> subgoals
