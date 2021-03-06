
(** {1 Queryable types for the LSP server} *)

open Sigs
type location = Loc.t

(** Some sort of object that can be observed via the LSP *)
class virtual t = object
  method virtual loc: location
  (** Location of this object *)

  method children: t Iter.t = Iter.empty
  (** Immediate children of this object, with smaller locations *)

  method virtual pp : unit Fmt.printer
  (** Print the object in a user-readable way. *)

  method def_loc : Loc.t option = None
  (** Location of the definition of this object, if any. *)
end
type queryable = t

module type S = sig
  type t
  val as_queryable : t -> queryable
end

let mk_pp ?def_loc ~loc ~pp x : t = object
  inherit t
  method loc=loc
  method pp out () = pp out x
  method! def_loc = def_loc
end
