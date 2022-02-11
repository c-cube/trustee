
(** Typing environment.

    The environment maps names to types, constants, meta constants, etc.
*)

open Common_
module TA = Type_ast

type t

val empty : t

val add_const : TA.Const.t -> t -> t

val find_const : Name.t -> t -> TA.Const.t option

val all_consts : t -> TA.Const.t Iter.t

val pp : t Fmt.printer

(* TODO: modules? merge? maybe not before hierarchical names *)

