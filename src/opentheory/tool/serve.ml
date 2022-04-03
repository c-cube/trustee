open Trustee_opentheory

module K = Trustee_core.Kernel
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
      meta [A.enctype "utf-8"];
      link [A.href "/static/main.css"; A.rel "stylesheet"];
      link [A.href "/static/bootstrap.css"; A.rel "stylesheet"];
    ];
    body [] [
      div[cls "container"] bod
    ];
  ]

let reply_page ~title html =
  H.Response.make_string @@ Ok (Html.to_string_top @@ mk_page ~title html)

let h_root server idx : unit =
  H.add_route_handler server H.Route.(return) @@ fun _req ->
  let@ () = top_wrap_ _req in
  let open Html in
  let res =
    let {OT.Idx.thy_by_name; articles; errors; _ } = idx in
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
  reply_page ~title:"opentheory" res

let h_thy server idx : unit =
  H.add_route_handler server
    H.Route.(exact "thy" @/ string_urlencoded @/ return) @@ fun thy_name _req ->
  let@ () = top_wrap_ _req in
  let thy = Idx.find_thy idx thy_name in
  let res =
    Html.(
      [
        h3[][txtf "Theory %s" thy_name];
        Thy_file.to_html thy
      ]
    )
  in
  reply_page ~title:(spf "theory %s" thy_name) res

let h_art server idx : unit =
  H.add_route_handler server
    H.Route.(exact "art" @/ string_urlencoded @/ return) @@ fun art _req ->
  let@ () = top_wrap_ _req in
  let art_file = Idx.find_article idx art in
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
  reply_page ~title:(spf "article %s" art) res

let serve (idx:OT.Idx.t) ~port : unit =
  let server = H.create ~port () in
  h_root server idx;
  h_thy server idx;
  h_art server idx;
  H.Dir.add_vfs server
    ~config:(H.Dir.config ~dir_behavior:H.Dir.Index_or_lists ())
    ~vfs:Static.vfs ~prefix:"static";
  Printf.printf "listen on http://localhost:%d/\n%!" port;
  match H.run server with
  | Ok () -> ()
  | Error e -> raise e
