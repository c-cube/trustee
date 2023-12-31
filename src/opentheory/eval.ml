(** {1 Evaluate theories} *)

open Common_
module Log = Trustee_core.Log

type 'a or_error = 'a Trustee_core.Error.or_error

let now () = Unix.gettimeofday ()

let since_s t = now () -. t

let unquote_str = Util.unquote_str

(* callbacks *)

class type callbacks =
  object
    method start_theory : string -> unit

    method done_theory : string -> ok:bool -> time_s:float -> unit

    method start_article : string -> unit

    method done_article : string -> Article.t -> time_s:float -> unit
  end

class default_callbacks : callbacks =
  object
    method start_theory _ = ()

    method done_theory _ ~ok:_ ~time_s:_ = ()

    method start_article _ = ()

    method done_article _ _ ~time_s:_ = ()
  end

class print_callbacks : callbacks =
  object
    method start_theory name = Fmt.printf "@{<blue>> check@} theory `%s`@." name

    method done_theory name ~ok ~time_s =
      if ok then
        Fmt.printf "@{<green>@<1>✔ checked@} theory `%s` in %.3fs@." name time_s
      else
        Fmt.printf "@{<error>@<1>× error@} theory `%s` in %.3fs@." name time_s

    method start_article art_name =
      Fmt.printf "@{<blue>> checking@} article '%s'@." art_name

    method done_article art_name art ~time_s =
      Fmt.printf "@{<green>@<1>✔ checked@} article `%s`: %a in %.3fs@." art_name
        Article.pp_stats art time_s
  end

(* ## main checking state ## *)

type eval_info = {
  info: string;
  time: float;
  sub: (string * eval_info) list;
}

let rec eval_info_to_html (self : eval_info) =
  Html.(
    table'
      [ cls "table table-sm" ]
      [
        sub_e
        @@ tr [] [ td [] [ txt "time:" ]; td [] [ txtf "%.3fs" self.time ] ];
        sub_e
        @@ tr [] [ td [] [ txt "info:" ]; td [] [ p [] [ txt self.info ] ] ];
        (if self.sub = [] then
          sub_empty
        else
          sub_l
            (List.map
               (fun (s, ei) ->
                 tr []
                   [
                     td [] [ txtf "sub.%s:" s ]; td [] [ eval_info_to_html ei ];
                   ])
               self.sub));
      ])

let mk_ei ~time ~info ?(sub = []) () : eval_info = { sub; time; info }

type state = {
  ctx: K.ctx;
  idx: Idx.t;
  progress_bar: bool;
  theories: (K.Theory.t * eval_info) or_error Str_tbl.t;
  cb: callbacks;
}

let create ?(cb = new default_callbacks) ?(progress_bar = false) ~ctx ~idx () :
    state =
  { ctx; idx; progress_bar; theories = Str_tbl.create 32; cb }

exception Exit of Trustee_core.Error.t

(* TODO: build interpretations *)

let interpr_of_sub (sub : Thy_file.sub) : K.Theory.interpretation =
  let i = sub.Thy_file.interp in
  Interp_file.items_iter i
  |> Iter.map (function
         | Interp_file.I_const (a, b) | Interp_file.I_ty (a, b) -> a, b)
  |> Str_map.of_iter

(* index individual content of theory *)
let add_theory_items (idx : Idx.t) (th : K.Theory.t) =
  let thms =
    Iter.append
      (K.Theory.param_theorems th |> Iter.of_list)
      (K.Theory.theorems th |> Iter.of_list)
  in

  let exprs = thms |> Iter.flat_map K.Thm.iter_exprs in
  let consts =
    Iter.concat
    @@ Iter.of_list
         [
           (* constants in any sub-term *)
           exprs
           |> Iter.flat_map (K.Expr.iter_dag' ~iter_ty:true)
           |> Iter.filter_map K.Expr.as_const
           |> Iter.map fst;
           K.Theory.param_consts th |> Iter.of_list;
           K.Theory.consts th |> Iter.of_list;
         ]
  in

  consts (fun c ->
      let h = K.Const.chash c in
      Chash.Tbl.replace idx.Idx.by_hash h (Idx.H_const c));

  thms (fun th ->
      K.Thm.make_main_proof th;
      let h = K.Thm.chash th in
      Chash.Tbl.replace idx.Idx.by_hash h (Idx.H_thm th));

  ()

(* check a theory *)
let rec eval_rec_ (self : state) (n : string) : K.Theory.t * eval_info =
  let th = Idx.find_thy self.idx n in
  let uv_name = Thy_file.name th in

  (* un-versioned name *)

  (* FIXME: just skip from there? or handle errors in the theory graph? *)
  (*   if uv_name = "group-witness" then Log.set_level 50; *)
  match Str_tbl.get self.theories uv_name with
  | Some (Error e) -> raise (Exit e)
  | Some (Ok th) -> th
  | None ->
    let eval_res =
      try Ok (eval_rec_real_ self uv_name th) with Exit e -> Error e
    in
    CCResult.iter (fun (th, _) -> add_theory_items self.idx th) eval_res;
    Str_tbl.add self.theories uv_name eval_res;
    (match eval_res with
    | Ok x -> x
    | Error e -> raise (Exit e))

and eval_rec_real_ (self : state) uv_name (th : Thy_file.t) :
    K.Theory.t * eval_info =
  self.cb#start_theory uv_name;

  (* process theories implementing requirements of this one requires *)
  let requires =
    List.map (fun r -> fst @@ process_requires_ self th r) th.requires
  in

  let t0 = now () in

  let main = th.Thy_file.main in
  (* start with `main` sub-package *)
  let res =
    try
      let r = check_sub_ ~requires self th main in
      Ok r
    with Exit e -> Error e
  in

  let ok = CCResult.is_ok res in
  self.cb#done_theory uv_name ~ok ~time_s:(since_s t0);

  match res with
  | Ok (theory, ei) ->
    Log.debugf 4 (fun k ->
        k "(@[@{<green>eval.success@}@ %a@])" K.Theory.pp theory);
    theory, ei
  | Error e ->
    Log.debugf 1 (fun k ->
        k "(@[@{<red>eval.failure@}@ %a@])" Trustee_core.Error.pp e);
    raise (Exit e)

(* check a sub-entry of a theory file *)
and check_sub_ (self : state) ~requires th (sub : Thy_file.sub) :
    K.Theory.t * eval_info =
  (* process imports *)
  let imports, subs =
    let l =
      List.map
        (fun i -> i, process_import_ ~requires self th i)
        sub.Thy_file.imports
    in
    List.map (fun (_, (th, _)) -> th) l, List.map (fun (s, (_, ei)) -> s, ei) l
  in
  assert (
    Option.is_none sub.Thy_file.package || Option.is_none sub.Thy_file.article);

  (* name to give the resulting theory *)
  let th_name =
    if sub.Thy_file.sub_name = "main" then
      th.Thy_file.name
    else
      Printf.sprintf "%s.%s" th.Thy_file.name sub.Thy_file.sub_name
  in

  match sub.Thy_file.package, sub.Thy_file.article with
  | Some _, Some _ ->
    Trustee_core.Error.failf (fun k ->
        k "block '%s' of theory '%s' has both article/package fields"
          sub.Thy_file.sub_name th.Thy_file.name)
  | None, None ->
    (* union of imports *)
    let t0 = now () in
    let r = K.Theory.union self.ctx ~name:th_name imports in

    let ei =
      mk_ei ~time:(since_s t0)
        ~info:(spf "union [%s]" (String.concat ", " @@ List.map fst subs))
        ()
    in
    r, ei
  | Some p, None ->
    (* package block *)
    let t0 = now () in
    let th_p, ei0 = eval_rec_ self p in
    let interp = interpr_of_sub sub in

    if imports = [] && Str_map.is_empty interp then
      th_p, ei0
    else if imports = [] then
      ( K.Theory.instantiate ~interp th_p,
        mk_ei
          ~time:(now () -. t0)
          ~info:"instantiate" ~sub:(("th", ei0) :: subs) () )
    else
      ( K.Theory.compose ~interp imports th_p,
        mk_ei
          ~time:(now () -. t0)
          ~info:
            (spf "compose %s with [%s]" p
               (String.concat ", " @@ List.map fst subs))
          ~sub:(("th", ei0) :: subs) () )
  | None, Some art_name ->
    (* article block *)
    let file =
      try Str_tbl.find self.idx.Idx.articles art_name
      with Not_found ->
        Trustee_core.Error.failf (fun k ->
            k "cannot find article `%s`" art_name)
    in

    let t0 = now () in

    (* VM for the article has both imports and requires in scope *)
    let vm =
      VM.create ~progress_bar:self.progress_bar self.ctx
        ~in_scope:(List.rev_append requires imports)
    in
    self.cb#start_article art_name;

    CCIO.with_in file (fun ic ->
        let input = VM.Input.of_chan ic in
        let th, art = VM.parse_and_check_art_exn ~name:art_name vm input in
        self.cb#done_article art_name art ~time_s:(since_s t0);
        Log.debugf 1 (fun k -> k "vm stats: %a" VM.pp_stats vm);
        let vm_stat = Fmt.to_string VM.pp_stats vm in
        let ei = mk_ei ~time:(since_s t0) ~info:vm_stat () in
        th, ei)

(* process an import of a sub, by checking it recursively now *)
and process_import_ (self : state) ~requires th (name : string) : K.Theory.t * _
    =
  let sub =
    try List.find (fun sub -> sub.Thy_file.sub_name = name) th.Thy_file.subs
    with Not_found ->
      Trustee_core.Error.failf (fun k -> k "cannot find sub-theory `%s`" name)
  in
  check_sub_ self ~requires th sub

(* process a require, looking for a theory with that name *)
and process_requires_ self _th (name : string) : K.Theory.t * _ =
  eval_rec_ self name

let eval_theory (self : state) name0 : (K.Theory.t * eval_info) or_error =
  try Ok (eval_rec_ self name0) with Exit e -> Error e
