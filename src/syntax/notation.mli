
(** Concrete notations for terms

    Each notation describes a variation on how to print/parse expressions using
    concrete names and infix precedences.
*)

open Common_
type fixity = Fixity.t

type t
(** Set of notations *)

val empty : t

(* TODO: also be able to rename constants, so we can use canonical
   names like Data.Bool./\ and print as `\land` or `∧` *)

val find : t -> Name.t -> fixity option
val find_name : t -> Name.t -> fixity option
val find_or_default : t -> Name.t -> fixity
val find_name_or_default : t -> Name.t -> fixity

val declare : Name.t -> fixity -> t -> t

val pp : t Fmt.printer

module Ref : sig
  type notation = t
  type nonrec t = notation ref

  val create : unit -> t
  val create_hol : unit -> t
  val of_notation : notation -> t

  val find : t -> Name.t -> fixity option
  val find_or_default : t -> Name.t -> fixity

  val declare : t -> Name.t -> fixity -> unit

  val pp : t Fmt.printer
end

(** ## HOL ## *)

val empty_hol : t


