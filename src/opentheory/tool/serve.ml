open Trustee_opentheory

module Log = Trustee_core.Log
module OT = Trustee_opentheory
open OT.Common_

let top_wrap_ req f =
  try f()
  with
  | Error.E e ->
    H.Response.make_string @@
    Error (404, Fmt.asprintf "internal error: %a" Error.pp e)

let mk_page ~title:title_ bod : Html.elt =
  let open Html in
  let bod =
    div [cls "navbar"] [
      ul[cls "navbar-nav"][
        li[cls "nav-item"][ a [A.href "/"] [txt "home"]];
      ]
    ]
    :: bod
  in
  html [] [
    head [] [
      title [] [txt title_];
      meta [A.charset "utf-8"];
      link [A.href "/static/bootstrap.css"; A.rel "stylesheet"];
      link [A.href "/static/main.css"; A.rel "stylesheet"];
      script [A.src "/static/htmx.js"] [];
    ];
    body [] [
      div[cls "container"] bod
    ];
  ]

let reply_page ~title req h =
  let headers = ["content-encoding", "utf-8"] in
  let res =
    if H.Headers.contains "hx-request" (H.Request.headers req) then (
      (* fragment *)
      Html.(to_string @@ div[cls"container"]h)
    ) else (
      Html.to_string_top @@ mk_page ~title h
    )
  in
  H.Response.make_string ~headers @@ Ok res

type state = {
  server: H.t;
  st: St.t;
}

let home_txt =
  Html.[
    p[][txt "Welcome to Trustee!"];
    p[][
      txt
        {|Trustee is a HOL kernel implemented in OCaml, with a few unusual design choices,
          such as the pervasive use of hashconsing, explicit type application,
          and de Bruijn indices.|}
    ];
    p[][
      a[A.href "https://github.com/c-cube/trustee"][txt "see on github."];
    ];
    p[][
      txt
        {| This website shows a proof-checker for |};
      a[A.href "http://www.gilith.com/opentheory/"][txt "opentheory"];
      txt {| using Trustee. This doubles as a test suite and gives an idea of
      how performant the tool is.|};
    ];
  ]

let h_root (self:state) : unit =
  H.add_route_handler self.server H.Route.(return) @@ fun req ->
  let@ () = top_wrap_ req in
  let open Html in
  let res =
    let {OT.Idx.thy_by_name; articles; errors; _ } = self.st.idx in
    [
      h2[][txt "Trustee"];
      div[] home_txt;
      a[A.href "/stats"][txt "context statistics"];
      h2[][ txt "theories"];
      ul'[A.class_ "list-group"] [
        sub_l (
          thy_by_name
          |> Str_tbl.to_list
          |> List.sort CCOrd.(map fst string)
          |> List.map
            (fun (name,_th) ->
               li [A.class_ "list-group-item"] [
                 a [A.href (spf "/thy/%s" (H.Util.percent_encode name))] [txt name];
               ]
            )
        )
      ]
    ]
  in
  reply_page ~title:"opentheory" req res

let h_thy (self:state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "thy" @/ string_urlencoded @/ return) @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let thy = Idx.find_thy self.st.idx thy_name in
  let res =
    let open Html in
    [
      div[cls "container"][
        h3[][txtf "Theory %s" thy_name];
        Thy_file.to_html thy;
        div [
          "hx-trigger", "load";
          "hx-get", (spf "/eval/%s" @@ H.Util.percent_encode thy_name);
          "hx-swap", "innerHtml"] [
          span[cls "htmx-indicator"; A.id "ind"][
            txt "[evaluating…]";
          ]
        ];
      ]
    ]
  in
  reply_page ~title:(spf "theory %s" thy_name) req res

let h_art (self:state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "art" @/ string_urlencoded @/ return) @@ fun art req ->
  let@ () = top_wrap_ req in
  let art_file =
    let@ () = St.with_lock self.st.lock in
    Idx.find_article self.st.idx art in
  let content = CCIO.with_in art_file CCIO.read_all in
  let res = Html.[
      a[A.href "http://www.gilith.com/opentheory/article.html"][txt "reference documentation"];
      h3[] [ txtf "Article %s" art ];
      p[][txtf "path: %S" art_file];
      details [][
        summary[][txtf "%d bytes" (String.length content)];
        pre[] [txt content]
      ]
    ]
  in
  reply_page ~title:(spf "article %s" art) req res

let h_eval (self:state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "eval" @/ string_urlencoded @/ return) @@ fun thy_name req ->
  let@ () = top_wrap_ req in
  let res =
    (* need lock around ctx/eval *)
    let@ () = St.with_lock self.st.lock in
    Eval.eval_theory self.st.eval thy_name
  in

  let config =
    let thy =
      let@ () = St.with_lock self.st.lock in
      Idx.find_thy self.st.idx thy_name in
    let open_namespaces =
      thy.Thy_file.meta
      |> List.filter_map (fun (mk,v) ->
          if mk="show" then Some (Util.unquote_str v ^ ".") else None)
    in
    Log.debugf 2 (fun k->k"open namespaces: [%s]" (String.concat "; " open_namespaces));
    Render.Config.make ~open_namespaces ()
  in

  let open Html in
  begin match res with
    | Ok (th,ei) ->
      let res = [
        h3[] [txt "Evaluation information"];
        Eval.eval_info_to_html ei;
        Render.theory_to_html ~config th;
      ] in
      reply_page ~title:(spf "eval %s" thy_name) req res
    | Error err ->
      let msg = Fmt.asprintf "%a" Error.pp err in
      H.Response.make_string (Error(500, msg))
  end

let h_hash_item (self:state) : unit =
  H.add_route_handler self.server
    H.Route.(exact "h" @/ string @/ return) @@ fun h req ->
  let@ () = top_wrap_ req in
  let h = Chash.of_string_exn h in
  let res =
    (* need lock around ctx/eval *)
    let@ () = St.with_lock self.st.lock in
    Chash.Tbl.find_opt self.st.idx.Idx.by_hash h
  in

  let r = match res with
    | Some r -> r
    | None -> Error.failf (fun k->k"hash not found: %a" Chash.pp h)
  in
  let config = Render.Config.make ~open_all_namespaces:true () in

  let open Html in
  let kind, res = match r with
    | Idx.H_const c ->
      "constant", [
        h3[] [txtf "constant %a" K.Const.pp c];
        pre[][Render.const_to_html ~config c];
        h4[] [txt "Definition"];
        Render.const_def_to_html ~config self.st.ctx c;
      ]
    | Idx.H_expr e ->
      "expression", [
        pre[][Render.expr_to_html ~config e]
      ]
    | Idx.H_thm thm ->
      "theorem", [
        h3[] [txt "theorem"];
        Render.thm_to_html ~config thm;
        h3[] [txt "proof"];
        Render.proof_to_html ~config thm;
      ]
  in
  reply_page ~title:(spf "%s %s" kind @@ Chash.to_string h) req res

let h_stats self : unit =
  H.add_route_handler self.server
    H.Route.(exact "stats" @/ return) @@ fun req ->
  let@ () = top_wrap_ req in
  let res =
    (* need lock around ctx/eval *)
    let@ () = St.with_lock self.st.lock in
    let n_exprs = K.Ctx.n_exprs self.st.ctx in
    let n_theories = List.length self.st.idx.Idx.theories in
    let n_hashes = Chash.Tbl.length self.st.idx.Idx.by_hash in
    Html.(
      table[cls "table table-striped table-sm"][
        tbody[][
          tr[][
            td[][txt "number of exprs"];
            td[][txtf "%d" n_exprs];
          ];
          tr[][
            td[][txt "number of theories"];
            td[][txtf "%d" n_theories];
          ];
          tr[][
            td[][txt "number of objects indexed by their hash"];
            td[][txtf "%d" n_hashes];
          ];

        ]
      ]
    )
  in
  reply_page ~title:"/stats" req [res]

let serve st ~port : unit =
  let server = H.create ~addr:"0.0.0.0" ~port () in
  Tiny_httpd_prometheus.(instrument_server server  global);
  let state = {server; st } in
  h_root state;
  h_thy state;
  h_art state;
  h_eval state;
  h_hash_item state;
  h_stats state;
  H.Dir.add_vfs server
    ~config:(H.Dir.config ~dir_behavior:H.Dir.Index_or_lists ())
    ~vfs:Static.vfs ~prefix:"static";
  Printf.printf "listen on http://localhost:%d/\n%!" port;
  match H.run server with
  | Ok () -> ()
  | Error e -> raise e
