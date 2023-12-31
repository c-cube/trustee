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

val find : t -> string -> fixity option

val find_name : t -> string -> fixity option

val find_or_default : t -> string -> fixity

val find_name_or_default : t -> string -> fixity

val declare : string -> fixity -> t -> t

val pp : t Fmt.printer

module Ref : sig
  type notation = t

  type nonrec t = notation ref

  val create : unit -> t

  val create_hol : unit -> t

  val of_notation : notation -> t

  val find : t -> string -> fixity option

  val find_or_default : t -> string -> fixity

  val declare : t -> string -> fixity -> unit

  val pp : t Fmt.printer
end

(** ## HOL ## *)

val empty_hol : t
