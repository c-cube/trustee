open Trustee_opentheory
module Log = Trustee_core.Log
module OT = Trustee_opentheory
open OT.Common_
module OTEL = Opentelemetry

let trace_middleware : H.Middleware.t =
 fun h req ~resp ->
  let@ _span = Trace.with_span ~parent:None ~__FILE__ ~__LINE__ "http.handle" in
  Trace.add_data_to_span _span
    [
      "http.path", `String req.path;
      "http.method", `String (H.Meth.to_string req.meth);
    ];
  let resp (response : H.Response.t) =
    let size =
      match response.body with
      | `String s -> [ "body.size", `Int (String.length s) ]
      | `Void -> [ "body.size", `Int 0 ]
      | `Stream _ | `Writer _ -> []
    in
    Trace.add_data_to_span _span
      (size @ [ "http.response.code", `Int response.code ]);
    resp response
  in
  try h req ~resp
  with exn ->
    let bt = Printexc.get_raw_backtrace () in
    Opentelemetry_trace.record_exception _span exn bt;
    Printexc.raise_with_backtrace exn bt

let top_wrap_ req f =
  try f ()
  with Error.E e ->
    H.Response.make_string
    @@ Error (404, Fmt.asprintf "internal error: %a" Error.pp e)

let mk_page ~title:title_ ~strip_ns ~strip_all bod : Html.elt =
  let open Html in
  let bod =
    div
      [ cls "navbar" ]
      [
        ul
          [ cls "navbar-nav" ]
          [ li [ cls "nav-item" ] [ a [ A.href "/" ] [ txt "home" ] ] ];
      ]
    :: bod
  in
  html []
    [
      head []
        [
          title [] [ txt title_ ];
          meta [ A.charset "utf-8" ];
          link [ A.href "/static/bootstrap.css"; A.rel "stylesheet" ];
          link [ A.href "/static/main.css"; A.rel "stylesheet" ];
          script [ A.src "/static/htmx.js" ] [];
          script [ A.src "/static/trustee-ui.js"; A.type_ "module" ] [];
        ];
      body
        [
          "data-strip-ns", String.concat "|" strip_ns;
          "data-strip-all", string_of_bool strip_all;
        ]
        [ div [ cls "container" ] bod ];
    ]

let reply_page ~title ?(strip_ns = []) ?(strip_all = false) req h =
  let headers = [ "content-encoding", "utf-8"; "content-type", "text/html" ] in
  let res =
    if H.Headers.contains "hx-request" (H.Request.headers req) then
      (* htmx fragments inherit body attrs from the host page (same theory). *)
      Html.(to_string @@ div [ cls "container" ] h)
    else
      Html.to_string_top @@ mk_page ~title ~strip_ns ~strip_all h
  in
  H.Response.make_string ~headers @@ Ok res

type state = {
  server: H.t;
  st: St.t;
  port: int;
}

module Dec = Trustee_minidag.Decode

let proof_thm_off (data : string) (lp_root : int) : int option =
  let dec = Dec.create data in
  try
    Some
      (Dec.read_node dec lp_root (fun nd _cmd ->
           let n = Int64.to_int (Dec.read_int64_exn nd) in
           if n <= 0 then failwith "empty lp";
           (* of_thm_proof emits parents first, so the theorem is the last step. *)
           let last = ref 0 in
           for _ = 1 to n do
             last := Dec.read_ref_exn nd
           done;
           Dec.read_node dec !last (fun nd _cmd -> Dec.read_ref_exn nd)))
  with _ -> None

let ce_ty_off (data : string) (ce_off : int) : int =
  let dec = Dec.create data in
  Dec.read_node dec ce_off (fun nd _cmd ->
      ignore (Dec.read_string_exn nd);
      Dec.read_ref_exn nd)

let strip_ns_of_config (config : Render.Config.t) : string list =
  List.map
    (fun s ->
      let n = String.length s in
      if n > 0 && s.[n - 1] = '.' then
        String.sub s 0 (n - 1)
      else
        s)
    config.Render.Config.open_namespaces

let proof_blob_url ~(v : int) thy idx =
  spf "/blob/proof/%s/%d?v=%d" (H.Util.percent_encode thy) idx v

let entry_blob_url ~(v : int) thy =
  spf "/blob/entry/%s?v=%d" (H.Util.percent_encode thy) v

let const_blob_url ~(v : int) thy c =
  spf "/blob/const/%s/%s?v=%d"
    (H.Util.percent_encode thy)
    (H.Util.percent_encode c) v

let home_txt =
  Html.
    [
      p [] [ txt "Welcome to Trustee!" ];
      p []
        [
          txt
            {|Trustee is a HOL kernel implemented in OCaml, with a few unusual design choices,
          such as the pervasive use of hashconsing, explicit type application,
          and de Bruijn indices.|};
        ];
      p []
        [
          a
            [ A.href "https://github.com/c-cube/trustee" ]
            [ txt "see on github." ];
        ];
      p []
        [
          txt {| This website shows a proof-checker for |};
          a [ A.href "http://www.gilith.com/opentheory/" ] [ txt "opentheory" ];
          txt
            {| using Trustee. This doubles as a test suite and gives an idea of
      how performant the tool is.|};
        ];
    ]

let h_root (self : state) : unit =
  H.add_route_handler self.server H.Route.(return) @@ fun req ->
  let@ () = top_wrap_ req in
  let open Html in
  let res =
    let { OT.Idx.thy_by_name; articles; errors; _ } = self.st.idx in
    [
      h2 [] [ txt "Trustee" ];
      div [] home_txt;
      a [ A.href "/stats" ] [ txt "context statistics" ];
      h2 [] [ txt "theories" ];
      ul'
        [ A.class_ "list-group" ]
        [
          sub_l
            (thy_by_name |> Str_tbl.to_list
            |> List.sort CCOrd.(map fst string)
            |> List.map (fun (name, _th) ->
                li
                  [ A.class_ "list-group-item" ]
                  [
                    a
                      [ A.href (spf "/thy/%s" (H.Util.percent_encode name)) ]
                      [ txt name ];
                  ]));
        ];
    ]
  in
  reply_page ~title:"opentheory" req res

let make_config_ self thy_name =
  let thy =
    let@ () = St.with_lock self.st.lock in
    Idx.find_thy self.st.idx thy_name
  in
  let open_namespaces =
    thy.Thy_file.meta
    |> List.filter_map (fun (mk, v) ->
        if mk = "show" then
          Some (Util.unquote_str v ^ ".")
        else
          None)
  in
  Log.debugf 2 (fun k ->
      k "open namespaces: [%s]" (String.concat "; " open_namespaces));
  Render.Config.make ~open_namespaces ()

let h_thy (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "thy" @/ string_urlencoded @/ return)
  @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let thy = Idx.find_thy self.st.idx thy_name in
  let config = make_config_ self thy_name in
  let res =
    let open Html in
    [
      div
        [ cls "container" ]
        [
          h3 [] [ txtf "Theory %s" thy_name ];
          Thy_file.to_html thy;
          div
            [
              "hx-trigger", "load";
              ( "hx-get",
                spf "/eval/%s" @@ H.Util.percent_encode thy.Thy_file.name );
              "hx-swap", "innerHtml";
            ]
            [
              span [ cls "htmx-indicator"; A.id "ind" ] [ txt "[evaluating…]" ];
            ];
        ];
    ]
  in
  reply_page ~title:(spf "theory %s" thy_name)
    ~strip_ns:(strip_ns_of_config config)
    req res

let h_art (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "art" @/ string_urlencoded @/ return)
  @@ fun art req ->
  let@ () = top_wrap_ req in
  let art_file =
    let@ () = St.with_lock self.st.lock in
    Idx.find_article self.st.idx art
  in
  let content = CCIO.with_in art_file CCIO.read_all in
  let res =
    Html.
      [
        a
          [ A.href "http://www.gilith.com/opentheory/article.html" ]
          [ txt "reference documentation" ];
        h3 [] [ txtf "Article %s" art ];
        p [] [ txtf "path: %S" art_file ];
        details []
          [
            summary [] [ txtf "%d bytes" (String.length content) ];
            pre [] [ txt content ];
          ];
      ]
  in
  reply_page ~title:(spf "article %s" art) req res

let h_eval (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "eval" @/ string_urlencoded @/ return)
  @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let config = make_config_ self thy_name in
  let open Html in
  let loaded =
    let@ () = St.with_lock self.st.lock in
    match St.load_theory self.st thy_name with
    | None -> None
    | Some th ->
      let const_offsets =
        let all = K.Theory.param_consts th @ K.Theory.consts th in
        match self.st.zip with
        | None -> Array.make (List.length all) None
        | Some zh ->
          (match Proof_zip.expr_offset_table zh thy_name with
          | None -> Array.make (List.length all) None
          | Some tbl ->
            Array.of_list
              (List.map (fun c -> K.Expr.Tbl.find_opt tbl (K.Const.ty c)) all))
      in
      let seq_offsets =
        let n =
          List.length (K.Theory.param_theorems th @ K.Theory.theorems th)
        in
        match self.st.zip with
        | None -> Array.make n None
        | Some zh ->
          (match Proof_zip.theory_offsets zh ~name:thy_name with
          | None -> Array.make n None
          | Some (_consts, seqs, _param_consts, param_seqs) ->
            Array.of_list
              (List.map
                 (fun x -> Some x)
                 (Array.to_list (Array.append param_seqs seqs))))
      in
      Some (th, const_offsets, seq_offsets)
  in
  match loaded with
  | None ->
    Log.debugf 1 (fun k -> k "theory not found in zip: %s" thy_name);
    H.Response.make_string
      (Error (404, spf "theory not found in zip: %s" thy_name))
  | Some (th, const_offsets, seq_offsets) ->
    let blob = entry_blob_url ~v:self.st.zip_v thy_name in
    let make_proof_link i =
      spf "/proof/%s/%d" (H.Util.percent_encode thy_name) i
    in
    let res =
      [
        h3 [] [ txt "Evaluation information" ];
        Eval.eval_info_to_html Eval.dummy_info;
        Render.theory_to_html ~config ~make_proof_link ~blob ~const_offsets
          ~seq_offsets th;
      ]
    in
    reply_page ~title:(spf "eval %s" thy_name)
      ~strip_ns:(strip_ns_of_config config)
      req res

let h_proof (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "proof" @/ string_urlencoded @/ string_urlencoded @/ return)
  @@ fun thy_name thm_idx_str req ->
  let@ () = top_wrap_ req in
  match int_of_string_opt thm_idx_str with
  | None ->
    H.Response.make_string
      (Error (400, spf "invalid theorem index: %s" thm_idx_str))
  | Some thm_idx ->
    let page =
      let@ () = St.with_lock self.st.lock in
      match self.st.zip with
      | None -> `Theory_not_found
      | Some zh ->
        (match Proof_zip.theory_offsets zh ~name:thy_name with
        | None -> `Theory_not_found
        | Some _ ->
          (match Proof_zip.proof_count zh ~name:thy_name with
          | None -> `Theory_not_found
          | Some 0 -> `No_proofs
          | Some n when thm_idx < 0 || thm_idx >= n -> `Out_of_bounds
          | Some _ ->
            (match
               Proof_zip.slice_proof_blob zh ~name:thy_name ~idx:thm_idx
             with
            | None -> `No_proofs
            | Some (data, lp_root) ->
              (match proof_thm_off data lp_root with
              | None -> `No_proofs
              | Some thm_off -> `Ok (lp_root, thm_off)))))
    in
    (match page with
    | `Theory_not_found ->
      H.Response.make_string (Error (404, spf "theory not found: %s" thy_name))
    | `No_proofs ->
      H.Response.make_string
        (Error (404, spf "no proofs available for: %s" thy_name))
    | `Out_of_bounds ->
      H.Response.make_string
        (Error (404, spf "theorem index out of bounds: %d" thm_idx))
    | `Ok (lp_root, thm_off) ->
      let config = make_config_ self thy_name in
      let blob = proof_blob_url ~v:self.st.zip_v thy_name thm_idx in
      let open Html in
      let res =
        [
          h3 [] [ txtf "Proof of theorem %d in %s" thm_idx thy_name ];
          div
            [ cls "mb-3" ]
            [
              strong [] [ txt "Theorem: " ];
              Render.island ~kind:"thm" ~blob ~off:thm_off;
            ];
          h4 [] [ txt "Proof steps" ];
          Render.island ~kind:"proof" ~blob ~off:lp_root;
        ]
      in
      reply_page
        ~title:(spf "proof %s/%d" thy_name thm_idx)
        ~strip_ns:(strip_ns_of_config config)
        req res)

let h_name_item (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "c" @/ string_urlencoded @/ return)
  @@ fun name req ->
  let@ () = top_wrap_ req in
  let found =
    let@ () = St.with_lock self.st.lock in
    match Idx.by_name_find self.st.idx name with
    | None -> None
    | Some item -> Some (item, Idx.origin_find self.st.idx name)
  in

  let r, origin =
    match found with
    | Some x -> x
    | None -> Error.failf (fun k -> k "name not found: %s" name)
  in
  let config = Render.Config.make ~open_all_namespaces:true () in

  let open Html in
  let kind, res =
    match r with
    | Idx.H_const c ->
      let cname = K.Const.name c in
      (match origin with
      | None ->
        Error.failf (fun k -> k "const not in a loaded theory: %s" cname)
      | Some (thy, _) ->
        let sliced =
          let@ () = St.with_lock self.st.lock in
          match self.st.zip with
          | None -> None
          | Some zh -> Proof_zip.slice_const_blob zh ~name:thy ~const:cname
        in
        (match sliced with
        | None -> Error.failf (fun k -> k "no blob for const: %s" cname)
        | Some (data, ce_off, def_part) ->
          let blob = const_blob_url ~v:self.st.zip_v thy cname in
          let ty_off = ce_ty_off data ce_off in
          let def_html =
            match def_part with
            | Some (def_root, "dt") ->
              p []
                [
                  txt "defined as: ";
                  Render.island ~kind:"term" ~blob ~off:def_root;
                ]
            | Some (def_root, "dty") ->
              p []
                [
                  txt "defined type with predicate: ";
                  Render.island ~kind:"term" ~blob ~off:def_root;
                ]
            | _ -> Render.const_def_to_html ~config self.st.ctx c
          in
          ( "constant",
            [
              h3 [] [ txtf "constant %a" K.Const.pp c ];
              pre []
                [
                  Render.const_head_html ~config c;
                  Render.island ~kind:"term" ~blob ~off:ty_off;
                ];
              h4 [] [ txt "Definition" ];
              def_html;
            ] )))
    | Idx.H_expr e -> "expression", [ pre [] [ Render.expr_to_html ~config e ] ]
    | Idx.H_thm thm ->
      let island_page =
        match origin with
        | Some (thy, idx) when idx >= 0 ->
          let sliced =
            let@ () = St.with_lock self.st.lock in
            match self.st.zip with
            | None -> None
            | Some zh -> Proof_zip.slice_proof_blob zh ~name:thy ~idx
          in
          (match sliced with
          | None -> None
          | Some (data, lp_root) ->
            (match proof_thm_off data lp_root with
            | None -> None
            | Some thm_off ->
              let blob = proof_blob_url ~v:self.st.zip_v thy idx in
              Some
                [
                  h3 [] [ txt "theorem" ];
                  div [] [ Render.island ~kind:"thm" ~blob ~off:thm_off ];
                  h3 [] [ txt "proof" ];
                  Render.island ~kind:"proof" ~blob ~off:lp_root;
                ]))
        | _ -> None
      in
      (match island_page with
      | Some res -> "theorem", res
      | None ->
        "theorem", [ h3 [] [ txt "theorem" ]; Render.thm_to_html ~config thm ])
  in
  reply_page ~title:(spf "%s %s" kind name) ~strip_all:true req res

let h_stats self : unit =
  H.add_route_handler self.server H.Route.(exact "stats" @/ return)
  @@ fun req ->
  let@ () = top_wrap_ req in
  let res =
    (* need lock around ctx/eval *)
    let@ () = St.with_lock self.st.lock in
    let n_exprs = K.Ctx.n_exprs self.st.ctx in
    let n_theories = List.length self.st.idx.Idx.theories in
    let n_names = Str_tbl.length self.st.idx.Idx.by_name in
    Html.(
      table
        [ cls "table table-striped table-sm" ]
        [
          tbody []
            [
              tr []
                [ td [] [ txt "number of exprs" ]; td [] [ txtf "%d" n_exprs ] ];
              tr []
                [
                  td [] [ txt "number of theories" ];
                  td [] [ txtf "%d" n_theories ];
                ];
              tr []
                [
                  td [] [ txt "number of objects indexed by name" ];
                  td [] [ txtf "%d" n_names ];
                ];
            ];
        ])
  in
  reply_page ~title:"/stats" req [ res ]

let blob_response data =
  H.Response.make_string
    ~headers:
      [
        "content-type", "application/octet-stream";
        "cache-control", "public, max-age=31536000, immutable";
      ]
    (Ok data)

let h_blob_proof (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(
      exact "blob" @/ exact "proof" @/ string_urlencoded @/ string_urlencoded
      @/ return)
  @@ fun thy_name idx_str req ->
  let@ () = top_wrap_ req in
  match int_of_string_opt idx_str with
  | None ->
    H.Response.make_string
      (Error (400, spf "invalid theorem index: %s" idx_str))
  | Some idx ->
    let res =
      let@ () = St.with_lock self.st.lock in
      match self.st.zip with
      | None -> None
      | Some zh -> Proof_zip.slice_proof_blob zh ~name:thy_name ~idx
    in
    (match res with
    | None ->
      H.Response.make_string
        (Error (404, spf "no proof blob for: %s/%d" thy_name idx))
    | Some (data, _root) -> blob_response data)

let h_blob_entry (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "blob" @/ exact "entry" @/ string_urlencoded @/ return)
  @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let res =
    let@ () = St.with_lock self.st.lock in
    match self.st.zip with
    | None -> None
    | Some zh -> Proof_zip.entry_bytes zh thy_name
  in
  match res with
  | None ->
    H.Response.make_string (Error (404, spf "no entry blob for: %s" thy_name))
  | Some data -> blob_response data

let h_blob_const (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(
      exact "blob" @/ exact "const" @/ string_urlencoded @/ string_urlencoded
      @/ return)
  @@ fun thy_name const_name req ->
  let@ () = top_wrap_ req in
  let res =
    let@ () = St.with_lock self.st.lock in
    match self.st.zip with
    | None -> None
    | Some zh -> Proof_zip.slice_const_blob zh ~name:thy_name ~const:const_name
  in
  match res with
  | None ->
    H.Response.make_string
      (Error (404, spf "no const blob for: %s/%s" thy_name const_name))
  | Some (data, _root, _def_root) -> blob_response data

let setup_otel () =
  OTEL.Globals.service_name := "trustee";
  Opentelemetry_client_ocurl.setup ();
  Opentelemetry_trace.setup ();
  OTEL.Gc_metrics.setup ~min_interval_s:60 ()

let create st ~addr ~port : state =
  setup_otel ();
  let server =
    H.create ~addr ~port ~middlewares:[ `Stage 1, trace_middleware ] ()
  in
  Tiny_httpd_camlzip.setup server;
  Tiny_httpd_prometheus.(instrument_server server global);
  let state = { server; st; port } in
  h_root state;
  h_thy state;
  h_art state;
  h_eval state;
  h_proof state;
  h_name_item state;
  h_stats state;
  h_blob_proof state;
  h_blob_entry state;
  h_blob_const state;
  H.Dir.add_vfs server
    ~config:(H.Dir.config ~dir_behavior:H.Dir.Index_or_lists ())
    ~vfs:Static.vfs ~prefix:"static";
  state

let active_connections (self : state) : int = H.active_connections self.server
let active (self : state) = H.running self.server

let serve (self : state) : unit =
  Printf.printf "listen on http://localhost:%d/\n%!" self.port;
  match H.run self.server with
  | Ok () -> ()
  | Error e ->
    H.stop self.server;
    raise e
  | exception e ->
    H.stop self.server;
    raise e
