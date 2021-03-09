
(** {1 Evaluate theories} *)

module K = Trustee_core.Kernel
module Log = Trustee_core.Log

let now() = Unix.gettimeofday()
let since_s t = now() -. t
let unquote_str = Util.unquote_str

(* callbacks *)

class type callbacks = object
  method start_theory : string -> unit
  method done_theory : string -> ok:bool -> time_s:float -> unit
  method start_article : string -> unit
  method done_article : string -> Article.t -> time_s:float -> unit
end

class default_callbacks : callbacks = object
  method start_theory _ = ()
  method done_theory _ ~ok:_ ~time_s:_ = ()
  method start_article _ = ()
  method done_article _ _ ~time_s:_ = ()
end

class print_callbacks : callbacks = object
  method start_theory name =
    Fmt.printf "@{<blue>> check@} theory `%s`@." name;
  method done_theory name ~ok ~time_s =
    if ok then (
      Fmt.printf "@{<green>@<1>✔ checked@} theory `%s` in %.3fs@." name time_s;
    ) else (
      Fmt.printf "@{<error>@<1>× error@} theory `%s` in %.3fs@." name time_s;
    )
  method start_article art_name =
    Fmt.printf "@{<blue>> checking@} article '%s'@." art_name;
  method done_article art_name art ~time_s =
    Fmt.printf "@{<green>@<1>✔ checked@} article `%s`: %a in %.3fs@."
      art_name Article.pp_stats art time_s;
end

(* ## main checking state ## *)

type state = {
  ctx: K.ctx;
  idx: Idx.t;
  vm: VM.t;
  theories: K.Theory.t or_error Str_tbl.t;
  cb: callbacks;
}

let create ?(cb=new default_callbacks) ?progress_bar ~ctx ~idx () : state =
  let vm = VM.create ?progress_bar ctx in
  {ctx; idx; theories=Str_tbl.create 32; vm; cb}

exception Exit of Trustee_error.t

let find_th_by_name_ self n =
  try Str_tbl.find self.idx.Idx.thy_by_name n
  with Not_found -> errorf (fun k->k"cannot find theory `%s`" n)

(* TODO: build interpretations *)

let interpr_of_sub (sub:Thy_file.sub) : K.Theory.interpretation =
  let i = sub.Thy_file.interp in
  Interp_file.items_iter i
  |> Iter.map
    (function
      | Interp_file.I_const (a,b)
      | Interp_file.I_ty (a,b) -> a,b)
  |> Str_map.of_iter

(* check a theory *)
let rec eval_rec_ (self:state) (n:string) : K.Theory.t =
  let th = find_th_by_name_ self n in
  let uv_name = Thy_file.name th in  (* un-versioned name *)

  begin match Str_tbl.get self.theories uv_name with
    | Some (Error e) -> raise (Exit e)
    | Some (Ok th) -> th
    | None ->
      let eval_res =
        try Ok (eval_rec_real_ self uv_name th)
        with Exit e -> Error e
      in
      Str_tbl.add self.theories uv_name eval_res;
      match eval_res with
      | Ok x -> x
      | Error e -> raise (Exit e)
  end

and eval_rec_real_ (self:state) uv_name (th:Thy_file.t) : K.Theory.t =
  self.cb#start_theory uv_name;

  (* process theories implementing requirements of this one requires *)
  List.iter (process_requires_ self th) th.requires;

  let t1 = now() in

  let main = th.Thy_file.main in (* start with `main` sub-package *)
  let res =
    try Ok (check_sub_ self th main)
    with Exit e -> Error e
  in

  let ok = CCResult.is_ok res in
  self.cb#done_theory uv_name ~ok ~time_s:(since_s t1);

  begin match res with
    | Ok theory ->
      Log.debugf 4 (fun k->k"(@[@{<green>eval.success@}@ %a@])" K.Theory.pp theory);
      theory
    | Error e ->
      Log.debugf 1 (fun k->k"(@[@{<red>eval.failure@}@ %a@])" Trustee_error.pp e);
      raise (Exit e)
  end

(* check a sub-entry of a theory file *)
and check_sub_ (self:state) th (sub:Thy_file.sub) : K.Theory.t =
  (* process imports *)
  let imports = List.map (process_import_ self th) sub.Thy_file.imports in
  assert (CCOpt.is_none sub.Thy_file.package || CCOpt.is_none sub.Thy_file.article);

  (* name to give the resulting theory *)
  let th_name =
    if sub.Thy_file.sub_name = "main"
    then th.Thy_file.name
    else Printf.sprintf "%s.%s" th.Thy_file.name sub.Thy_file.sub_name
  in

  begin match sub.Thy_file.package, sub.Thy_file.article with
    | Some _, Some _ ->
      errorf
        (fun k->k"block '%s' of theory '%s' has both article/package fields"
            sub.Thy_file.sub_name th.Thy_file.name)
    | None, None ->
      (* union of imports *)
      K.Theory.union self.ctx ~name:th_name imports

    | Some p, None ->
      (* package block *)
      let th_p = eval_rec_ self p in
      let interp = interpr_of_sub sub in
      if imports=[] && Str_map.is_empty interp then th_p
      else if imports=[] then K.Theory.instantiate ~interp:interp th_p
      else K.Theory.compose ~interp:interp imports th_p

    | None, Some art_name ->
      (* article block *)
      let art_name = unquote_str art_name in
      let file =
        try Str_tbl.find self.idx.Idx.articles art_name
        with Not_found ->
          errorf(fun k->k"cannot find article `%s`" art_name)
      in

      let t1 = now () in
      self.cb#start_article art_name;

      VM.clear_article self.vm;
      VM.clear_dict self.vm;

      CCIO.with_in file
        (fun ic ->
           let input = VM.Input.of_chan ic in
           let th, art = VM.parse_and_check_art_exn ~name:art_name self.vm input in
           self.cb#done_article art_name art ~time_s:(since_s t1);
           Log.debugf 1 (fun k->k"vm stats: %a" VM.pp_stats self.vm);
           th
        )
  end

(*
  (* find package, if any *)
  CCOpt.iter (fun p -> check_ p) sub.Thy_file.package;
  (* find and check article, if any *)
  CCOpt.iter (fun art_name ->
      let art_name = unquote_str art_name in
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
   *)

(* process an import of a sub, by checking it recursively now *)
and process_import_ (self:state) th (name:string) : K.Theory.t =
  let name = unquote_str name in
  let sub =
    try List.find (fun sub -> sub.Thy_file.sub_name=name) th.Thy_file.subs
    with Not_found -> errorf(fun k->k"cannot find sub-theory `%s`" name)
  in
  check_sub_ self th sub

(* process a require, looking for a theory with that name *)
and process_requires_ self _th (name:string) : unit =
  ignore (eval_rec_ self name : K.Theory.t)

(*
  let by_name = idx.Idx.thy_by_name in
  let checked = Str_tbl.create 32 in
  let ctx = K.Ctx.create () in

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

   *)

let eval_theory (self:state) name0 : K.Theory.t or_error =
  try Ok (eval_rec_ self name0)
  with Exit e -> Error e
