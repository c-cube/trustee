(** {1 Index the OpenTheory development}

    The index is used to list all thy/int/art files and build the dependency
    graph among them. *)

open Common_

type path = string

type hashed_item =
  | H_const of K.Const.t
  | H_expr of K.Expr.t
  | H_thm of K.Thm.t

type by_name_entry
(** An entry of [by_name]; expires after [by_name_ttl_s] idle. *)

val by_name_ttl_s : float

type t = {
  theories: (path * Thy_file.t) list;
  thy_by_name: Thy_file.t Str_tbl.t;
  interps: (path * Interp_file.t) list;
  interp_by_name: Interp_file.t Str_tbl.t;
  articles: path Str_tbl.t; (* basename -> path *)
  errors: (path * Trustee_core.Error.t) list;
  by_name: by_name_entry Str_tbl.t;
  origin: (string * int) Str_tbl.t;
}
(** Results of listing a directory *)

val list_dir : path -> t
val find_thy : t -> string -> Thy_file.t
val find_article : t -> string -> string

val by_name_sweep : t -> unit
(** Drop expired [by_name] entries. *)

val by_name_add : t -> string -> hashed_item -> unit
(** Add or refresh a [by_name] entry. *)

val by_name_find : t -> string -> hashed_item option
(** Look up a [by_name] entry, refreshing its expiry. *)

val origin_add : t -> string -> string -> int -> unit
(** Remember that [key] (a const name or thm string) lives in theory [thy] at
    index [idx] ([-1] for consts). No TTL: blob routing needs it to outlive
    [by_name], and values are small. Param theorems are not recorded (they have
    no proofs of their own). *)

val origin_find : t -> string -> (string * int) option
