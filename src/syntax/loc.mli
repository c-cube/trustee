
(** Full location *)

module LL = Local_loc

type t

val pp : t Fmt.printer

val none : t
val make : ctx:LL.ctx -> LL.t -> t

val filename : t -> string
val positions : t -> Position.t * Position.t
val contains : t -> Position.t -> bool

val local_loc : t -> Local_loc.t
val same_local_loc : t -> t -> bool

val union : t -> t -> t
val union_l : t -> f:('a -> t) -> 'a list -> t

module Infix : sig
  val (++) : t -> t -> t
  (** Short for {!union} *)
end

include module type of Infix