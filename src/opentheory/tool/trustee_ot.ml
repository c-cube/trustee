
open Trustee_opentheory

module K = Trustee_core.Kernel
module G = CCGraph
module Log = Trustee_core.Log

let print_all idx =
  let {Idx.errors; theories; interps; _} = idx in 
  List.iter
    (fun (s,thy) -> Fmt.printf "%s: %s@." s thy.Thy_file.name)
    theories;
  List.iter
    (fun (s,int) -> Fmt.printf "interp %s (%d lines)@." s (Interp_file.size int))
    interps;
  List.iter
    (fun (s,e) -> Fmt.printf "@{<Red>Error@} for %s: %a@." s Trustee_error.pp e)
    errors;
  ()

let now() = Unix.gettimeofday()
let since_s t = now() -. t

type edge =
  | E_requires
  | E_sub

(* index theories by their name and versioned name *)
type theories = {
  theories: (string, Thy_file.t) Hashtbl.t;
}

(* make a graph *)
let mk_graph ~sub theories : _ G.t =
  let tbl: (string, Thy_file.t) Hashtbl.t =
    theories
    |> Iter.flat_map_l (fun th -> [th.Thy_file.name, th; Thy_file.versioned_name th, th])
    |> CCHashtbl.of_iter
  in
  let find_ s =
    try Hashtbl.find tbl s
    with Not_found -> errorf (fun k->k"theory not found: '%s'" s)
  in
  G.make
    (fun th ->
       Iter.append
         (Thy_file.requires th |> Iter.of_list |> Iter.map (fun s -> E_requires, find_ s))
         (if sub then Thy_file.sub_packages th |> Iter.of_list |> Iter.map (fun s -> E_sub, find_ s) else Iter.empty))

let sort_all (theories:Thy_file.t Iter.t) : unit =
  let g = mk_graph ~sub:true theories in
  Iter.iter
    (fun th ->
       let edges =
         g th
         |> Iter.filter (fun (s,_) -> s=E_requires)
         |> Iter.map snd
         |> Iter.map Thy_file.name
         |> Iter.to_rev_list in
       Fmt.printf "%s: %s@." th.Thy_file.name (String.concat "," edges))
    theories;
  let l =
    G.topo_sort ~rev:true
      ~eq:Thy_file.equal ~tbl:(G.mk_table ~eq:Thy_file.equal ~hash:Thy_file.hash 32) ~graph:g
      theories
  in
  List.iter (fun th -> Fmt.printf "%s@." th.Thy_file.name) l;
  ()

let print_dot file (theories:Thy_file.t Iter.t) =
  let g = mk_graph ~sub:false theories in
  CCIO.with_out file
    (fun oc ->
       let out = Format.formatter_of_out_channel oc in
       G.Dot.pp_all
         ~attrs_v:(fun th -> [`Label th.name; `Shape "box"])
         ~attrs_e:(function
             | E_requires -> [`Label "requires"]
             | E_sub -> [`Label "sub"; `Style "dotted"])
         ~eq:Thy_file.equal ~tbl:(G.mk_table ~eq:Thy_file.equal ~hash:Thy_file.hash 32)
         ~graph:g out theories;
       Fmt.fprintf out "@.");
  ()

let unquote_str = Util.unquote_str

let check_ (idx:Idx.t) ~progress_bar ~names : unit =
  let by_name = idx.Idx.thy_by_name in
  let checked = Str_tbl.create 32 in
  let ctx = K.Ctx.create () in
  let vm = VM.create ~progress_bar ctx in

  let find_by_name n =
    try Str_tbl.find by_name n
    with Not_found -> errorf (fun k->k"cannot find theory `%s`" n)
  in

  (* check a theory *)
  let rec check_ (n:string) =
    let th = find_by_name n in
    let uv_name = Thy_file.name th in  (* un-versioned name *)

    if not (Str_tbl.mem checked uv_name) then (
      Str_tbl.add checked uv_name ();
      Fmt.printf "@{<blue>> check@} theory `%s`@." uv_name;

      (* process requires *)
      List.iter (process_requires_ th) th.requires;

      let t1 = now() in

      let main = th.Thy_file.main in (* start with `main` sub-package *)
      check_sub_ th main;

      Fmt.printf "@{<green>@<1>✔ checked@} theory `%s` in %.3fs@." uv_name (since_s t1);
    )
  (* check a sub-entry of a theory *)
  and check_sub_ th (sub:Thy_file.sub) : unit =
    (* process imports *)
    List.iter (process_import_ th) sub.Thy_file.imports;
    (* find package, if any *)
    CCOpt.iter (fun p -> check_ p) sub.Thy_file.package;
    (* find and check article, if any *)
    CCOpt.iter (fun art_name ->
        let art_name = unquote_str art_name in
(*         if art_name = "sum-def.art" then Log.set_level 50; (* XXX *) *)
(*         if art_name = "relation-natural-thm.art" then Log.set_level 10; (* XXX *) *)
        let file =
          try Str_tbl.find idx.Idx.articles art_name
          with Not_found ->
            errorf(fun k->k"cannot find article `%s`" art_name)
        in

        let t1 = now () in
        Fmt.printf "@{<blue>> checking@} article '%s'@." art_name;
        CCIO.with_in file
          (fun ic ->
             let input = VM.Input.of_chan ic in
             let art = VM.parse_and_check_art_exn vm input in
             Fmt.printf "@{<green>@<1>✔ checked@} article: %a in %.3fs@."
               Article.pp_stats art (since_s t1);
             Log.debugf 1 (fun k->k"vm stats: %a" VM.pp_stats vm);
          );
      )
      sub.Thy_file.article;
    ()

  (* process a require, looking for a theory with that name *)
  and process_requires_ _th (name:string) : unit =
    check_ name

  (* process an import of a sub, by checking it recursively now *)
  and process_import_ th (name:string) : unit =
    let name = unquote_str name in
    let sub =
      try List.find (fun sub -> sub.Thy_file.sub_name=name) th.Thy_file.subs
      with Not_found -> errorf(fun k->k"cannot find sub-theory `%s`" name)
    in
    check_sub_ th sub
  in
  Iter.iter check_ names;
  ()

let sort = ref false
let print = ref false
let dot_file = ref ""
let check = ref []
let check_all = ref false
let progress_ = ref false

let main ~dir () =
  let idx =
    let t1 = now() in
    let r = Idx.list_dir dir in
    Fmt.printf "indexed `%s` in %.3fs@." dir (since_s t1);
    r
  in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Idx.theories |> Iter.map snd in
  if !sort then (
    sort_all theories;
  );
  if !dot_file <> "" then (
    print_dot !dot_file theories;
  );
  if !check_all then (
    check_ idx
      ~progress_bar:!progress_ ~names:(Iter.map Thy_file.name theories); 
  ) else if !check <> [] then (
    check_ idx
      ~progress_bar:!progress_ ~names:(Iter.of_list !check)
  );
  ()

let () =
  let dir = ref "" in
  let opts = [
    "-dir", Arg.Set_string dir, " set opentheory directory";
    "-sort", Arg.Set sort, " print a topological sort of the theories";
    "-print", Arg.Set print, " print the list of theories";
    "-check", Arg.Rest (fun s->check := s :: !check), " check given theories";
    "-check-all", Arg.Set check_all, " check all";
    "-dot", Arg.Set_string dot_file, " print graph into file";
    "-d", Arg.Int Log.set_level, " set debug level";
    "--progress", Arg.Set progress_, " progress bar";
    "-p", Arg.Set progress_, " progress bar";
    "--bt", Arg.Unit (fun()->Printexc.record_backtrace true), " record backtraces";
  ] |> Arg.align in
  Arg.parse opts (fun _ -> failwith "invalid option") "trustee_ot [option*]";
  Fmt.set_color_default true;
  main ~dir:!dir ()
