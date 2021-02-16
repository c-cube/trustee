
(** {1 Theory files} *)

type sub = {
  sub_name: string;
  imports: string list;
  package: string option;
}

type t = {
  name: string;
  version: string;
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

val parse : t P.t
val of_string : string -> t or_error

(** {2 List content of a directory} *)
module List_dir : sig
  type thy = t
  type path = string

  (** Results of listing a directory *)
  type t = {
    theories: (path * thy) list;
    errors: (path * Trustee_error.t) list;
  }

  val list_dir : path -> t
end
