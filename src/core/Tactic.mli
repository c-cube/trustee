module Make(C : Core.S) : sig
  open C.KoT
  module Goal : module type of struct include Goal.Make(C) end

  type goal = Goal.t
  type subgoals = goal list * (Thm.t list -> Thm.t)

  type t = goal -> subgoals
end
