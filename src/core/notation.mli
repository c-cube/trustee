
(** {1 Concrete notations for terms}

    Each notation describes a variation on how to print/parse expressions using
    concrete names and infix precedences.
*)

open Sigs

module K = Kernel
type fixity = Fixity.t
type t

val empty : t

(* TODO: also be able to rename constants, so we can use canonical
   names like Data.Bool./\ and print as `\land` or `∧` *)

val find : t -> string -> fixity option
val find_name : t -> K.Name.t -> fixity option
val find_or_default : t -> string -> fixity
val find_name_or_default : t -> K.Name.t -> fixity

val declare : string -> fixity -> t -> t

val pp : t Fmt.printer

module Ref : sig
  type notation = t
  type nonrec t = notation ref

  val create : unit -> t
  val of_notation : notation -> t

  val find : t -> string -> fixity option
  val find_or_default : t -> string -> fixity

  val declare : t -> string -> fixity -> unit

  val pp : t Fmt.printer
end

(** ## HOL ## *)

val empty_hol : t


(** {3 Print Exprs} *)

val pp_expr : t -> K.Expr.t Fmt.printer

