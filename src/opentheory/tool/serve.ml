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
  lock: Mutex.t;
  server: H.t;
  idx: Idx.t;
  eval: Eval.state;
}

let[@inline] with_lock l f =
  Mutex.lock l;
  Fun.protect ~finally:(fun () -> Mutex.unlock l) f

let h_root (self:state) : unit =
  H.add_route_handler self.server H.Route.(return) @@ fun req ->
  let@ () = top_wrap_ req in
  let open Html in
  let res =
    let {OT.Idx.thy_by_name; articles; errors; _ } = self.idx in
    [
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
  let thy = Idx.find_thy self.idx thy_name in
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
            txt "evaluating…]";
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
  let art_file = Idx.find_article self.idx art in
  let content = CCIO.with_in art_file CCIO.read_all in
  let res = Html.[
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
    let@ () = with_lock self.lock in
    Eval.eval_theory self.eval thy_name
  in

  let config =
    let thy = Idx.find_thy self.idx thy_name in
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

let serve (idx:OT.Idx.t) ~port : unit =
  let server = H.create ~port () in
  let ctx = K.Ctx.create () in
  let eval = Eval.create ~ctx ~idx () in
  let state = {idx; server; eval; lock=Mutex.create(); } in
  h_root state;
  h_thy state;
  h_art state;
  h_eval state;
  H.Dir.add_vfs server
    ~config:(H.Dir.config ~dir_behavior:H.Dir.Index_or_lists ())
    ~vfs:Static.vfs ~prefix:"static";
  Printf.printf "listen on http://localhost:%d/\n%!" port;
  match H.run server with
  | Ok () -> ()
  | Error e -> raise e
