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
    Trace.add_data_to_span _span [ "http.response.code", `Int response.code ];
    resp response
  in
  h req ~resp

let top_wrap_ req f =
  try f ()
  with Error.E e ->
    H.Response.make_string
    @@ Error (404, Fmt.asprintf "internal error: %a" Error.pp e)

let mk_page ~title:title_ bod : Html.elt =
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
          script [ A.src "/static/tooltip.js" ] [];
        ];
      body [] [ div [ cls "container" ] bod ];
    ]

let reply_page ~title req h =
  let headers = [ "content-encoding", "utf-8"; "content-type", "text/html" ] in
  let res =
    if H.Headers.contains "hx-request" (H.Request.headers req) then
      (* fragment *)
      Html.(to_string @@ div [ cls "container" ] h)
    else
      Html.to_string_top @@ mk_page ~title h
  in
  H.Response.make_string ~headers @@ Ok res

type state = {
  server: H.t;
  st: St.t;
  port: int;
}

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

let h_thy (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "thy" @/ string_urlencoded @/ return)
  @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let thy = Idx.find_thy self.st.idx thy_name in
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
  reply_page ~title:(spf "theory %s" thy_name) req res

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

let h_eval (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "eval" @/ string_urlencoded @/ return)
  @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let config = make_config_ self thy_name in
  let open Html in
  (* Try zip first, fall back to live eval *)
  let zip_result =
    let@ () = St.with_lock self.st.lock in
    St.load_theory self.st thy_name
  in
  match zip_result with
  | Some th ->
    let make_proof_link i =
      spf "/proof/%s/%d" (H.Util.percent_encode thy_name) i
    in
    let res =
      [
        h3 [] [ txt "Evaluation information" ];
        Eval.eval_info_to_html Eval.dummy_info;
        Render.theory_to_html ~config ~make_proof_link th;
      ]
    in
    reply_page ~title:(spf "eval %s" thy_name) req res
  | None ->
    Log.debugf 1 (fun k -> k "theory not found in zip: %s" thy_name);
    H.Response.make_string
      (Error (404, spf "theory not found in zip: %s" thy_name))

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
    let config = make_config_ self thy_name in
    let th_opt, proofs_opt =
      let@ () = St.with_lock self.st.lock in
      let th = St.load_theory self.st thy_name in
      let proofs =
        match self.st.zip with
        | None -> None
        | Some zh -> Proof_zip.load_proofs zh ~ctx:self.st.ctx thy_name
      in
      th, proofs
    in
    (match th_opt, proofs_opt with
    | None, _ ->
      H.Response.make_string (Error (404, spf "theory not found: %s" thy_name))
    | _, None ->
      H.Response.make_string
        (Error (404, spf "no proofs available for: %s" thy_name))
    | Some th, Some proofs ->
      (match
         ( List.nth_opt (K.Theory.theorems th) thm_idx,
           List.nth_opt proofs thm_idx )
       with
      | None, _ | _, None ->
        H.Response.make_string
          (Error (404, spf "theorem index out of bounds: %d" thm_idx))
      | Some thm, Some lp ->
        let thy_entry = thy_name in
        let type_offsets =
          match self.st.zip with
          | None -> None
          | Some zh -> Proof_zip.expr_offset_table zh thy_entry
        in
        let open Html in
        let res =
          [
            h3 [] [ txtf "Proof of theorem %d in %s" thm_idx thy_name ];
            div
              [ cls "mb-3" ]
              [
                strong [] [ txt "Theorem: " ];
                Render.thm_to_html ~config ?type_offsets ~entry:thy_entry thm;
              ];
            h4 [] [ txt "Proof steps" ];
            Render.linear_proof_to_html ~config ?type_offsets ~entry:thy_entry
              lp;
          ]
        in
        reply_page ~title:(spf "proof %s/%d" thy_name thm_idx) req res))

let h_name_item (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "c" @/ string_urlencoded @/ return)
  @@ fun name req ->
  let@ () = top_wrap_ req in
  let res =
    (* need lock around ctx/eval *)
    let@ () = St.with_lock self.st.lock in
    Str_tbl.find_opt self.st.idx.Idx.by_name name
  in

  let r =
    match res with
    | Some r -> r
    | None -> Error.failf (fun k -> k "name not found: %s" name)
  in
  let config = Render.Config.make ~open_all_namespaces:true () in

  let open Html in
  let kind, res =
    match r with
    | Idx.H_const c ->
      ( "constant",
        [
          h3 [] [ txtf "constant %a" K.Const.pp c ];
          pre [] [ Render.const_to_html ~config c ];
          h4 [] [ txt "Definition" ];
          Render.const_def_to_html ~config self.st.ctx c;
        ] )
    | Idx.H_expr e -> "expression", [ pre [] [ Render.expr_to_html ~config e ] ]
    | Idx.H_thm thm ->
      ( "theorem",
        [
          h3 [] [ txt "theorem" ];
          Render.thm_to_html ~config thm;
          h3 [] [ txt "proof" ];
          Render.proof_to_html ~config thm;
        ] )
  in
  reply_page ~title:(spf "%s %s" kind name) req res

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

(** Render a single expression node (by minidag offset) as an HTML fragment.
    Route: GET /render/<entry>/<offset> Used by the hover tooltip JS to lazily
    fetch type strings. *)
let h_render (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "render" @/ string_urlencoded @/ string_urlencoded @/ return)
  @@ fun entry offset_str req ->
  let@ () = top_wrap_ req in
  match int_of_string_opt offset_str with
  | None ->
    H.Response.make_string (Error (400, spf "invalid offset: %s" offset_str))
  | Some offset ->
    let config = make_config_ self entry in
    let result =
      let@ () = St.with_lock self.st.lock in
      match self.st.zip with
      | None -> None
      | Some zh ->
        Option.map
          (fun e -> Render.expr_to_html ~config e)
          (Proof_zip.decode_expr_at zh ~ctx:self.st.ctx ~entry ~offset)
    in
    (match result with
    | None ->
      H.Response.make_string
        (Error (404, spf "expr not found at offset %d in %s" offset entry))
    | Some elt -> H.Response.make_string (Ok (Html.to_string elt)))

(** Render a sequent node (by minidag offset) as an HTML fragment. Route: GET
    /render_seq/<entry>/<offset> *)
let h_render_seq (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(
      exact "render_seq" @/ string_urlencoded @/ string_urlencoded @/ return)
  @@ fun entry offset_str req ->
  let@ () = top_wrap_ req in
  match int_of_string_opt offset_str with
  | None ->
    H.Response.make_string (Error (400, spf "invalid offset: %s" offset_str))
  | Some offset ->
    let config = make_config_ self entry in
    let result =
      let@ () = St.with_lock self.st.lock in
      match self.st.zip with
      | None -> None
      | Some zh ->
        Option.map
          (fun seq -> Render.sequent_to_html ~config seq)
          (Proof_zip.decode_seq_at zh ~ctx:self.st.ctx ~entry ~offset)
    in
    (match result with
    | None ->
      H.Response.make_string
        (Error (404, spf "seq not found at offset %d in %s" offset entry))
    | Some elt -> H.Response.make_string (Ok (Html.to_string elt)))

let setup_otel () =
  Opentelemetry_client_ocurl.setup ();
  Opentelemetry_trace.setup ();
  OTEL.Gc_metrics.setup ~min_interval_s:60 ()

let create st ~port : state =
  setup_otel ();
  let server =
    H.create ~addr:"127.0.0.1" ~port
      ~middlewares:[ `Stage 1, trace_middleware ]
      ()
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
  h_render state;
  h_render_seq state;
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
