(** Stream of tokens

    Imitation of stdlib's {!Stream}, specialized for parsing.
    It provides limited lookahead. *)

type 'a t

type is_done = bool

val create : next:(unit -> 'a * Loc.t * is_done) -> unit -> 'a t

val is_done : _ t -> is_done

val cur : 'a t -> 'a * Loc.t

val next : 'a t -> 'a * Loc.t

val consume : _ t -> unit

val iter : 'a t -> 'a Iter.t
(** Mostly intended for debugging. *)

val to_list : 'a t -> 'a list
(** Mostly intended for debugging. *)
