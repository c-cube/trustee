
open Trustee_opentheory

module Thy = OT_thy
module Article = OT_parser.Article
module G = CCGraph

let print_all idx =
  let {OT_thy.List_dir.errors; theories} = idx in 
  List.iter
    (fun (s,thy) -> Fmt.printf "%s: %s@." s thy.OT_thy.name)
    theories;
  List.iter
    (fun (s,e) -> Fmt.printf "@{<Red>Error@} for %s: %a@." s Trustee_error.pp e)
    errors;
  ()

type edge =
  | E_requires
  | E_sub

(* make a graph *)
let mk_graph ~sub theories : _ G.t =
  (* index theories by their name and versioned name *)
  let tbl: (string, Thy.t) Hashtbl.t =
    theories
    |> Iter.flat_map_l (fun th -> [th.Thy.name, th; Thy.versioned_name th, th])
    |> CCHashtbl.of_iter
  in
  let find_ s =
    try Hashtbl.find tbl s
    with Not_found -> errorf (fun k->k"theory not found: '%s'" s)
  in
  G.make
    (fun th ->
       Iter.append
         (Thy.requires th |> Iter.of_list |> Iter.map (fun s -> E_requires, find_ s))
         (if sub then Thy.sub_packages th |> Iter.of_list |> Iter.map (fun s -> E_sub, find_ s) else Iter.empty))

let sort_all (theories:Thy.t Iter.t) : unit =
  let g = mk_graph ~sub:true theories in
  Iter.iter
    (fun th ->
       let edges =
         g th
         |> Iter.filter (fun (s,_) -> s=E_requires)
         |> Iter.map snd
         |> Iter.map Thy.name
         |> Iter.to_rev_list in
       Fmt.printf "%s: %s@." th.Thy.name (String.concat "," edges))
    theories;
  let l =
    G.topo_sort ~rev:true
      ~eq:Thy.equal ~tbl:(G.mk_table ~eq:Thy.equal ~hash:Thy.hash 32) ~graph:g
      theories
  in
  List.iter (fun th -> Fmt.printf "%s@." th.Thy.name) l;
  ()

let print_dot file (theories:Thy.t Iter.t) =
  let g = mk_graph ~sub:false theories in
  CCIO.with_out file
    (fun oc ->
       let out = Format.formatter_of_out_channel oc in
       G.Dot.pp_all
         ~attrs_v:(fun th -> [`Label th.name; `Shape "box"])
         ~attrs_e:(function
             | E_requires -> [`Label "requires"]
             | E_sub -> [`Label "sub"; `Style "dotted"])
         ~eq:Thy.equal ~tbl:(G.mk_table ~eq:Thy.equal ~hash:Thy.hash 32)
         ~graph:g out theories;
       Fmt.fprintf out "@.");
  ()

let sort = ref false
let print = ref false
let dot_file = ref ""

let main ~dir () =
  let idx = OT_thy.List_dir.list_dir dir in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Thy.List_dir.theories |> Iter.map snd in
  if !sort then (
    sort_all theories;
  );
  if !dot_file <> "" then (
    print_dot !dot_file theories;
  );
  ()

let () =
  let dir = ref "" in
  let opts = [
    "-dir", Arg.Set_string dir, " set opentheory directory";
    "-sort", Arg.Set sort, " print a topological sort of the theories";
    "-print", Arg.Set print, " print the list of theories";
    "-dot", Arg.Set_string dot_file, " print graph into file";
  ] |> Arg.align in
  Arg.parse opts (fun _ -> failwith "invalid option") "trustee_ot [option*]";
  Fmt.set_color_default true;
  main ~dir:!dir ()
