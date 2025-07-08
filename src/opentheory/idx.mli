(** {1 Index the OpenTheory development}

    The index is used to list all thy/int/art files and build the dependency
    graph among them. *)

open Common_

type path = string

type hashed_item =
  | H_const of K.Const.t
  | H_expr of K.Expr.t
  | H_thm of K.Thm.t

type t = {
  theories: (path * Thy_file.t) list;
  thy_by_name: Thy_file.t Str_tbl.t;
  interps: (path * Interp_file.t) list;
  interp_by_name: Interp_file.t Str_tbl.t;
  articles: path Str_tbl.t; (* basename -> path *)
  errors: (path * Trustee_core.Error.t) list;
  by_hash: hashed_item Chash.Tbl.t;
}
(** Results of listing a directory *)

val list_dir : path -> t
val find_thy : t -> string -> Thy_file.t
val find_article : t -> string -> string
