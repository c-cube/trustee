
type path = string

(** Results of listing a directory *)
type t = {
  theories: (path * Thy_file.t) list;
  by_name: Thy_file.t Str_tbl.t;
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
  let by_name = Str_tbl.create 32 in
  let articles = Str_tbl.create 8 in
  let g = CCIO.File.walk dir in
  let module E = Trustee_error in
  G.iter g
    ~f:(fun (k,file) ->
        if k=`File && CCString.suffix ~suf:".thy" file then (
          try
            let s = CCIO.File.read_exn file in
            match Thy_file.of_string s with
            | Ok thy ->
              Str_tbl.add by_name thy.name thy;
              Str_tbl.add by_name (Thy_file.versioned_name thy) thy;
              theories := (file,thy) :: !theories
            | Error e -> errors := (file,e) :: !errors
          with e ->
            errors := (file, Trustee_error.mk (Printexc.to_string e)) :: !errors;
        ) else if k=`File && CCString.suffix ~suf:".art" file then (
          let base = Filename.basename file in
          Str_tbl.add articles base file;
        ));
  { theories= !theories; by_name; articles; errors= !errors; }
