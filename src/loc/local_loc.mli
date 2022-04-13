(** Locations

    A location is a range between two positions in a string (a source file).
*)

(** Context for the locations.

    The context provides information that is common to all locations within
    the same file, allowing each location to fit in one integer. *)
type ctx = private {
  str: string;
  filename: string;
  input: Loc_input.t;
  index: Line_index.t lazy_t;
}

val create : filename:string -> string -> ctx

type t = private int

val none : t

val make : ctx:ctx -> off1:int -> off2:int -> t
val make_pos : ctx:ctx -> Position.t -> Position.t -> t
val of_lexbuf : ctx:ctx -> Lexing.lexbuf -> t
val of_lex_pos : ctx:ctx -> Lexing.position -> Lexing.position -> t
val tr_position : ctx:ctx -> left:bool -> offset:int -> Lexing.position
val offset_of_pos : ctx:ctx -> Position.t -> int
val pos_of_offset : ctx:ctx -> int -> Position.t
val offsets : t -> int * int
val positions : ctx:ctx -> t -> Position.t * Position.t

val add_offset : off:int -> t -> t
(** [add_offset ~off loc] is [loc], shifted so that its offset
    0 actually starts at [off]. *)

val pp : ctx:ctx -> t Fmt.printer

val contains : t -> off:int -> bool

val equal : t -> t -> bool

val union : t -> t -> t
val union_l : t -> f:('a -> t) -> 'a list -> t

module Infix : sig
  val (++) : t -> t -> t
  (** Short for {!union} *)
end

include module type of Infix

