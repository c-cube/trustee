
type path = string

(* TODO: interpretations *)

(** Results of listing a directory *)
type t = {
  theories: (path * Thy_file.t) list;
  thy_by_name: Thy_file.t Str_tbl.t;
  interps: (path * Interp_file.t) list;
  interp_by_name: Interp_file.t Str_tbl.t;
  articles: path Str_tbl.t; (* basename -> path *)
  errors: (path * Trustee_error.t) list;
}

(* gen util(s) *)
module G = struct
  let rec iter ~f g = match g() with
    | Some x -> f x; iter ~f g
    | None -> ()
end

let list_dir dir : t =
  let errors = ref [] in
  let theories = ref [] in
  let interp = ref [] in
  let thy_by_name = Str_tbl.create 32 in
  let interp_by_name = Str_tbl.create 32 in
  let articles = Str_tbl.create 8 in
  let g = CCIO.File.walk dir in
  let module E = Trustee_error in

  let parse_thy file =
    let dir = Filename.dirname file in
    try
      let s = CCIO.File.read_exn file in
      match Thy_file.of_string ~dir s with
      | Ok thy ->
        Str_tbl.add thy_by_name thy.name thy;
        Str_tbl.add thy_by_name (Thy_file.versioned_name thy) thy;
        theories := (file,thy) :: !theories
      | Error e -> errors := (file,e) :: !errors
    with e ->
      errors := (file, Trustee_error.mk (Printexc.to_string e)) :: !errors;
  in

  let parse_interp file =
    let name = Filename.basename file in
    try
      let s = CCIO.File.read_exn file in
      match Interp_file.of_string s with
      | Ok int ->
        Str_tbl.add interp_by_name name int;
        interp := (file,int) :: !interp
      | Error e -> errors := (file,e) :: !errors
    with e ->
      errors := (file, Trustee_error.mk (Printexc.to_string e)) :: !errors;
  in

  let handle_file (k,file) =
    if k=`File && CCString.suffix ~suf:".thy" file then (
      parse_thy file
    ) else if k=`File && CCString.suffix ~suf:".int" file then (
      parse_interp file
    ) else if k=`File && CCString.suffix ~suf:".art" file then (
      let base = Filename.basename file in
      Str_tbl.add articles base file;
    )
  in
  G.iter g ~f:handle_file;
  { theories= !theories; thy_by_name; interp_by_name; interps= !interp;
    articles; errors= !errors; }
