(** A symbolic identifier for a runtime in a file.

    This should be stable when parsing the same file several times, and can be
    used to "name" nameless items such as "eval". *)

module Component : sig
  type t =
    | Str of string
    | Int of int

  val equal : t -> t -> bool
  val compare : t -> t -> int
end

type t = private {
  path: Component.t list;
  name: Component.t;
}

type sym_ptr = t

val str : string -> t
val pos : int -> t
val namespace : string -> t -> t

include Sigs.EQ with type t := t
include Sigs.HASH with type t := t
include Sigs.PP with type t := t
module Tbl : CCHashtbl.S with type key = t

module Map : sig
  type +'a t

  val empty : 'a t
  val find : sym_ptr -> 'a t -> 'a option

  val find_exn : sym_ptr -> 'a t -> 'a
  (** @raise Not_found if key not present *)

  val find_sub : sym_ptr -> 'a t -> 'a t option

  val find_sub_exn : sym_ptr -> 'a t -> 'a t
  (** @raise Not_found if key not present *)

  val add : sym_ptr -> 'a -> 'a t -> 'a t
  val namespace : string -> 'a t -> 'a t
  val add_with_namespace : string -> sub:'a t -> 'a t -> 'a t
  val to_iter : 'a t -> (sym_ptr * 'a) Iter.t
end
