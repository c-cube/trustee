open Common_

type path = string

(* TODO: interpretations *)

type hashed_item =
  | H_const of K.Const.t
  | H_expr of K.Expr.t
  | H_thm of K.Thm.t

(* by_name entries expire after a while, so a visited theory's consts and
   theorems don't stay pinned forever *)
type by_name_entry = {
  mutable bn_item: hashed_item;
  mutable bn_last_use: Mtime.t;
}

let by_name_ttl_s = 30.

type t = {
  theories: (path * Thy_file.t) list;
  thy_by_name: Thy_file.t Str_tbl.t;
  interps: (path * Interp_file.t) list;
  interp_by_name: Interp_file.t Str_tbl.t;
  articles: path Str_tbl.t; (* basename -> path *)
  errors: (path * Trustee_core.Error.t) list;
  by_name: by_name_entry Str_tbl.t;
}
(** Results of listing a directory *)

let find_thy (self : t) name : Thy_file.t =
  try Str_tbl.find self.thy_by_name name
  with Not_found -> Error.failf (fun k -> k "cannot find theory %S" name)

let find_article self name : string =
  try Str_tbl.find self.articles name
  with Not_found -> Error.failf (fun k -> k "cannot find article %S" name)

(* Drop expired by_name entries. *)
let by_name_sweep (self : t) : unit =
  let now = Mtime_clock.now () in
  let dead = ref [] in
  Str_tbl.iter
    (fun name e ->
      if
        Mtime.Span.to_float_ns (Mtime.span e.bn_last_use now) /. 1e9
        >= by_name_ttl_s
      then
        dead := name :: !dead)
    self.by_name;
  List.iter (Str_tbl.remove self.by_name) !dead

let by_name_add (self : t) (name : string) (item : hashed_item) : unit =
  let now = Mtime_clock.now () in
  match Str_tbl.find_opt self.by_name name with
  | Some e ->
    e.bn_item <- item;
    e.bn_last_use <- now
  | None ->
    Str_tbl.replace self.by_name name { bn_item = item; bn_last_use = now }

let by_name_find (self : t) (name : string) : hashed_item option =
  match Str_tbl.find_opt self.by_name name with
  | Some e ->
    if
      Mtime.Span.to_float_ns (Mtime.span e.bn_last_use (Mtime_clock.now ()))
      /. 1e9
      >= by_name_ttl_s
    then (
      Str_tbl.remove self.by_name name;
      None
    ) else (
      e.bn_last_use <- Mtime_clock.now ();
      Some e.bn_item
    )
  | None -> None

(* gen util(s) *)
module G = struct
  let rec iter ~f g =
    match g () with
    | Some x ->
      f x;
      iter ~f g
    | None -> ()
end

let list_dir dir : t =
  let@ _sp =
    Trace.with_span ~__FILE__ ~__LINE__ "trustee.idx.list-dir" ~data:(fun () ->
        [ "dir", `String dir ])
  in
  let errors = ref [] in
  let theories = ref [] in
  let interp = ref [] in
  let thy_by_name = Str_tbl.create 32 in
  let interp_by_name = Str_tbl.create 32 in
  let articles = Str_tbl.create 8 in
  let g = CCIO.File.walk dir in

  let parse_thy file =
    let@ _sp =
      Trace.with_span ~__FILE__ ~__LINE__ "trustee.idx.parse-thy"
        ~data:(fun () -> [ "file", `String file ])
    in
    let dir = Filename.dirname file in
    try
      if CCString.prefix ~pre:"group" (Filename.basename file) then
        failwith "SKIP GROUP";

      (* FIXME *)
      let s = CCIO.File.read_exn file in
      match Thy_file.of_string ~dir s with
      | Ok thy ->
        Str_tbl.add thy_by_name thy.name thy;
        Str_tbl.add thy_by_name (Thy_file.versioned_name thy) thy;
        theories := (file, thy) :: !theories
      | Error e -> errors := (file, e) :: !errors
    with e -> errors := (file, Trustee_core.Error.of_exn e) :: !errors
  in

  let parse_interp file =
    let@ _sp =
      Trace.with_span ~__FILE__ ~__LINE__ "trustee.idx.parse-interp"
        ~data:(fun () -> [ "file", `String file ])
    in
    let name = Filename.basename file in
    try
      let s = CCIO.File.read_exn file in
      match Interp_file.of_string s with
      | Ok int ->
        Str_tbl.add interp_by_name name int;
        interp := (file, int) :: !interp
      | Error e -> errors := (file, e) :: !errors
    with e -> errors := (file, Trustee_core.Error.of_exn e) :: !errors
  in

  let handle_file (k, file) =
    if k = `File && CCString.suffix ~suf:".thy" file then
      parse_thy file
    else if k = `File && CCString.suffix ~suf:".int" file then
      parse_interp file
    else if k = `File && CCString.suffix ~suf:".art" file then (
      let base = Filename.basename file in
      Str_tbl.add articles base file
    )
  in
  G.iter g ~f:handle_file;
  {
    theories = !theories;
    thy_by_name;
    interp_by_name;
    interps = !interp;
    articles;
    errors = !errors;
    by_name = Str_tbl.create 32;
  }
