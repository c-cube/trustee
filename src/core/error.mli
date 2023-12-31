(** Main error type *)

open Sigs

module type S = Error_intf.S

module type LOC = Error_intf.LOC

module Make (Loc : LOC) : S with type loc = Loc.t

module Conv
    (E : S)
    (E2 : S) (Conv : sig
      val conv : E.loc -> E2.loc option
    end) : sig
  val conv : E.t -> E2.t
end

include S with type loc = unit
