
(** {1 Stream of tokens}

    Imitation of stdlib's {!Stream}. *)

type 'a t
type loc = Loc.t
type is_done = bool

val create :
  next:(unit -> 'a * loc * is_done) ->
  unit -> 'a t

val is_done : _ t -> is_done

val cur : 'a t -> 'a * loc

val next : 'a t -> 'a * loc

val junk : _ t -> unit

val to_list : 'a t -> 'a list
