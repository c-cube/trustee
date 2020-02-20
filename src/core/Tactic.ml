
module Make(C : Core.S) = struct
  open C.KoT
  module Goal = Goal.Make(C)

  type goal = Goal.t
  type subgoals = goal list * (Thm.t list -> Thm.t)

  type t = goal -> subgoals
end
