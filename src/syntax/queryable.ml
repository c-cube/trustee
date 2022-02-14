
(** Queryable types for the LSP server.

    A queryable type is one that the user can query
    in various ways, the primary one being "hover". Other ways
    are LSP classics such as "go to definition", "infer type", etc.

*)

type location = Loc.t

(** Some sort of object that can be observed via the LSP *)
class virtual t = object
  method virtual loc: location
  (** Location of this object *)

  method children: t Iter.t = Iter.empty
  (** Immediate children of this object, normally with smaller (contained)
      locations *)

  method virtual pp : unit Fmt.printer
  (** Print the object in a user-readable way.
      This is useful for hover queries. *)

  method def_loc : Loc.t option = None
  (** Location of the definition of this object, if any.
      This is useful for go-to-def queries. *)

  method defining : (string * Loc.t) Iter.t = Iter.empty
  (** Symbols defined/bound in this object, if any.
      This is useful for listing symbols in a side-view or hierarchy. *)
end

type queryable = t

let pp out (self:t) = self#pp out ()
let loc (self:t) = self#loc
let children (self:t) : _ Iter.t = self#children
let def_loc (self:t) : _ option = self#def_loc
let defining (self:t) : _ Iter.t = self#defining

(** Queryable type. *)
module type S = sig
  type t
  val as_queryable : t -> queryable
end

(** Build a queryable object from a value, along with a printer
    and a location. *)
let mk_pp ?def_loc ?(defining=Iter.empty) ~loc ~pp x : t = object
  inherit t
  method loc=loc
  method pp out () = pp out x
  method! def_loc = def_loc
  method! defining = defining
end
