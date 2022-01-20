
(** {1 Theory files} *)

type sub = {
  sub_name: string;
  imports: string list;
  package: string option;
  article: string option;
  interp: Interp_file.t; (* file + individual lines *)
}

type t = {
  name: string;
  version: string;
  requires: string list;
  meta: (string * string) list;
  subs: sub list;
  main: sub;
}

val pp_sub : sub Fmt.printer
val pp : t Fmt.printer

val equal : t -> t -> bool
val hash : t -> int

val name : t -> string
val versioned_name : t -> string

val requires : t -> string list
(** Direct imports of this theory *)

val sub_packages : t -> string list
(** Sub-packages for this theory. *)

module P = CCParse

val parse : dir:string -> t P.t
val of_string : dir:string -> string -> t Trustee_core.Error.or_error

