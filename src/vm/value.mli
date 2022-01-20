
module K = Trustee_core.Kernel

type t
(** Universal values for the VM. *)

type value = t

val equal : t -> t -> bool
val hash : t -> int
val pp : t Fmt.printer

(** Values built from a particular concrete type *)
module type SPECIALIZED = sig
  type concrete
  type nonrec t = private t
  (** Specialized values, holding a {!concrete} item inside. *)

  val make : concrete -> t
  (** Build a new value from this item *)

  val get : t -> concrete
  (** Unwrap the value to obtain its concrete content *)

  val cast : value -> concrete option
  (** Try to cast an arbitrary into this *)
end

val make_specialized :
  pp:'a Fmt.printer ->
  equal:('a -> 'a -> bool) ->
  hash:('a -> int) ->
  unit ->
  (module SPECIALIZED with type concrete = 'a)

module Bool : SPECIALIZED with type concrete = bool
module Int : SPECIALIZED with type concrete = int
module Expr : SPECIALIZED with type concrete = K.Expr.t
module Thm : SPECIALIZED with type concrete = K.Thm.t
module Subst : SPECIALIZED with type concrete = K.Subst.t
