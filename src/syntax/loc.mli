(** Locations

    A location is a range between two positions in a string (a source file).
*)

module Fmt = CCFormat

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
val of_lexbuf : ctx:ctx -> Lexing.lexbuf -> t
val tr_position : ctx:ctx -> left:bool -> int -> Lexing.position
val offsets : t -> int * int

val pp : ctx:ctx -> t Fmt.printer

val union : t -> t -> t

module Infix : sig
  val (++) : t -> t -> t
  (** Short for {!union} *)
end

include module type of Infix

