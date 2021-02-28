
(** {1 Index the OpenTheory development}

    The index is used to list all thy/int/art files and build the dependency
    graph among them. *)

type path = string

(** Results of listing a directory *)
type t = {
  theories: (path * Thy_file.t) list;
  (* TODO: interpretation files *)
  by_name: Thy_file.t Str_tbl.t;
  articles: path Str_tbl.t; (* basename -> path *)
  errors: (path * Trustee_error.t) list;
}

val list_dir : path -> t
