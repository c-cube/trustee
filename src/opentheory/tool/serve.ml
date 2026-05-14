open Trustee_opentheory
module Log = Trustee_core.Log
module Vec = Trustee_core.Vec
module OT = Trustee_opentheory
open OT.Common_

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
          script [ A.src "/static/proof.js" ] [];
        ];
      body [] [ div [ cls "container" ] bod ];
    ]

let reply_page ~title req h =
  let headers = [ "content-encoding", "utf-8" ] in
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

(* ---- Helpers duplicated from render.ml (not exported) ---- *)

let strip_name_json_ ~config (s : string) : string =
  if config.Render.Config.open_all_namespaces then (
    match List.rev (String.split_on_char '.' s) with
    | c :: _ -> c
    | [] -> s
  ) else (
    match
      List.find
        (fun pre -> CCString.prefix ~pre s)
        config.Render.Config.open_namespaces
    with
    | pre -> CCString.chop_prefix ~pre s |> Option.get_exn_or "strip name"
    | exception Not_found -> s
  )

let is_symbol_json_ s =
  let anum = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
    | _ -> false
  in
  not (String.length s > 0 && anum s.[0])

let is_a_binder_json_ c c_name =
  is_symbol_json_ c_name
  &&
  match K.Expr.unfold_arrow @@ K.Const.ty c with
  | [ a ], _ret -> K.Expr.is_arrow a
  | _ -> false

let is_infix_json_ c c_name =
  is_symbol_json_ c_name
  &&
  match K.Expr.unfold_arrow @@ K.Const.ty c with
  | [ _; _ ], _ -> true
  | _ -> false

(* ---- JSON serialisation helpers ---- *)

let json_buf_string (buf : Buffer.t) (s : string) : unit =
  Buffer.add_char buf '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | c when Char.code c < 32 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04X" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.add_char buf '"'

let json_int (buf : Buffer.t) (n : int) : unit =
  Buffer.add_string buf (string_of_int n)

(* ----- Build the terms array for a proof ----- *)

type term_entry =
  | TE_type
  | TE_const of {
      name: string;
      short: string;
      href: string;
      ty: int;
      is_infix: bool;
      is_binder: bool;
      ty_args: int list;
    }
  | TE_var of {
      name: string;
      ty: int;
    }
  | TE_bvar of {
      idx: int;
      ty: int;
    }
  | TE_app of {
      f: int;
      a: int;
    }
  | TE_lam of {
      name: string;
      ty: int;
      body: int;
    }
  | TE_arrow of {
      a: int;
      b: int;
    }
  | TE_eq of {
      ty: int;
      l: int;
      r: int;
    }

let percent_encode_json s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '-' | '_' | '.' | '~' ->
        Buffer.add_char buf c
      | c -> Buffer.add_string buf (Printf.sprintf "%%%02X" (Char.code c)))
    s;
  Buffer.contents buf

let proof_to_json (lp : K.Linear_proof.t) (config : Render.Config.t) : string =
  let tbl : int K.Expr.Tbl.t = K.Expr.Tbl.create 256 in
  let entries : term_entry Vec.t = Vec.create () in

  let rec intern2 (e : K.Expr.t) : int =
    match K.Expr.Tbl.find_opt tbl e with
    | Some id -> id
    | None ->
      let id = Vec.size entries in
      K.Expr.Tbl.add tbl e id;
      Vec.push entries TE_type;
      (* placeholder *)
      let entry =
        match K.Expr.view e with
        | K.E_kind | K.E_type -> TE_type
        | K.E_var v ->
          let ty_id = intern2 v.v_ty in
          TE_var { name = v.v_name; ty = ty_id }
        | K.E_bound_var bv ->
          let ty_id = intern2 bv.bv_ty in
          TE_bvar { idx = bv.bv_idx; ty = ty_id }
        | K.E_const (c, args) ->
          let full_name = K.Const.name c in
          let short_name = strip_name_json_ ~config full_name in
          let href = "/c/" ^ percent_encode_json full_name in
          let ty_id = intern2 (K.Expr.ty_exn e) in
          let is_inf = is_infix_json_ c short_name in
          let is_bind = is_a_binder_json_ c short_name in
          let ty_args = List.map intern2 args in
          TE_const
            {
              name = full_name;
              short = short_name;
              href;
              ty = ty_id;
              is_infix = is_inf;
              is_binder = is_bind;
              ty_args;
            }
        | K.E_app _ ->
          (* Unfold the app chain *)
          let f_expr, args_list = K.Expr.unfold_app e in
          (match K.Expr.view f_expr, args_list with
          | K.E_const (c, [ _ty_arg ]), [ a; b ]
            when String.equal (K.Const.name c) "=" ->
            (* equality: emit as special = node *)
            let ty_id = intern2 (K.Expr.ty_exn f_expr) in
            let l_id = intern2 a in
            let r_id = intern2 b in
            TE_eq { ty = ty_id; l = l_id; r = r_id }
          | _ ->
            (* Regular app: only store the immediate f/a from the original view *)
            let f_e, a_e =
              match K.Expr.view e with
              | K.E_app (f, a) -> f, a
              | _ -> assert false
            in
            let f_id = intern2 f_e in
            let a_id = intern2 a_e in
            TE_app { f = f_id; a = a_id })
        | K.E_lam (name, ty, body) ->
          let ty_id = intern2 ty in
          let body_id = intern2 body in
          TE_lam { name; ty = ty_id; body = body_id }
        | K.E_arrow (a, b) ->
          let a_id = intern2 a in
          let b_id = intern2 b in
          TE_arrow { a = a_id; b = b_id }
        | K.E_box _ -> TE_type
      in
      Vec.set entries id entry;
      id
  in

  let intern_expr e = ignore (intern2 e : int) in

  (* Collect all exprs from steps *)
  K.Linear_proof.steps lp
  |> Iter.iter (fun (_idx, step) ->
         let seq = step.K.Linear_proof.concl in
         K.Sequent.hyps_l seq |> List.iter intern_expr;
         intern_expr (K.Sequent.concl seq);
         step.K.Linear_proof.args
         |> List.iter (function
              | K.Proof.Pr_expr e -> intern_expr e
              | K.Proof.Pr_subst pairs ->
                List.iter
                  (fun (v, e) ->
                    intern_expr (K.Var.ty v);
                    intern_expr e)
                  pairs));

  (* For Pr_subst vars we need to assign IDs to the vars themselves.
     We use a separate var tbl keyed by (name, ty_id). *)
  let var_tbl : (string * int, int) Hashtbl.t = Hashtbl.create 16 in
  let n_terms = ref (Vec.size entries) in
  let var_entries : term_entry Vec.t = Vec.create () in

  let intern_subst_var (v : K.Var.t) : int =
    let ty_id =
      match K.Expr.Tbl.find_opt tbl v.v_ty with
      | Some id -> id
      | None -> -1 (* shouldn't happen after we interned all types *)
    in
    let key = v.v_name, ty_id in
    match Hashtbl.find_opt var_tbl key with
    | Some id -> id
    | None ->
      let id = !n_terms + Vec.size var_entries in
      Hashtbl.add var_tbl key id;
      Vec.push var_entries (TE_var { name = v.v_name; ty = ty_id });
      id
  in

  (* --- Pass 2: build step records --- *)
  let steps_arr :
      (int list
      * int
      * string
      * int list
      * [ `E of int | `S of (int * int) list ] list)
      list =
    K.Linear_proof.steps lp
    |> Iter.map (fun (_idx, step) ->
           let seq = step.K.Linear_proof.concl in
           let hyp_ids =
             K.Sequent.hyps_l seq
             |> List.map (fun e ->
                    match K.Expr.Tbl.find_opt tbl e with
                    | Some id -> id
                    | None -> -1)
           in
           let concl_id =
             match K.Expr.Tbl.find_opt tbl (K.Sequent.concl seq) with
             | Some id -> id
             | None -> -1
           in
           let rule = step.K.Linear_proof.rule in
           let parents = step.K.Linear_proof.parents in
           let args =
             step.K.Linear_proof.args
             |> List.map (function
                  | K.Proof.Pr_expr e ->
                    let eid =
                      match K.Expr.Tbl.find_opt tbl e with
                      | Some id -> id
                      | None -> -1
                    in
                    `E eid
                  | K.Proof.Pr_subst pairs ->
                    let ps =
                      List.map
                        (fun (v, e) ->
                          let vid = intern_subst_var v in
                          let eid =
                            match K.Expr.Tbl.find_opt tbl e with
                            | Some id -> id
                            | None -> -1
                          in
                          vid, eid)
                        pairs
                    in
                    `S ps)
           in
           hyp_ids, concl_id, rule, parents, args)
    |> Iter.to_list
  in

  (* --- Serialise --- *)
  let buf = Buffer.create (16 * 1024) in
  Buffer.add_string buf "{\"terms\":";

  let n_exprs = Vec.size entries in
  let n_vars = Vec.size var_entries in
  let total = n_exprs + n_vars in

  Buffer.add_char buf '[';
  let emit_entry i te =
    if i > 0 then Buffer.add_char buf ',';
    match te with
    | TE_type -> Buffer.add_string buf "{\"k\":\"type\"}"
    | TE_const { name; short; href; ty; is_infix; is_binder; ty_args } ->
      Buffer.add_string buf "{\"k\":\"const\",\"name\":";
      json_buf_string buf name;
      Buffer.add_string buf ",\"short\":";
      json_buf_string buf short;
      Buffer.add_string buf ",\"href\":";
      json_buf_string buf href;
      Buffer.add_string buf ",\"ty\":";
      json_int buf ty;
      if is_infix then Buffer.add_string buf ",\"infix\":true";
      if is_binder then Buffer.add_string buf ",\"binder\":true";
      if ty_args <> [] then (
        Buffer.add_string buf ",\"args\":[";
        List.iteri
          (fun j aid ->
            if j > 0 then Buffer.add_char buf ',';
            json_int buf aid)
          ty_args;
        Buffer.add_char buf ']'
      );
      Buffer.add_char buf '}'
    | TE_var { name; ty } ->
      Buffer.add_string buf "{\"k\":\"var\",\"name\":";
      json_buf_string buf name;
      Buffer.add_string buf ",\"ty\":";
      json_int buf ty;
      Buffer.add_char buf '}'
    | TE_bvar { idx; ty } ->
      Buffer.add_string buf "{\"k\":\"bvar\",\"idx\":";
      json_int buf idx;
      Buffer.add_string buf ",\"ty\":";
      json_int buf ty;
      Buffer.add_char buf '}'
    | TE_app { f; a } ->
      Buffer.add_string buf "{\"k\":\"app\",\"f\":";
      json_int buf f;
      Buffer.add_string buf ",\"a\":";
      json_int buf a;
      Buffer.add_char buf '}'
    | TE_lam { name; ty; body } ->
      Buffer.add_string buf "{\"k\":\"lam\",\"name\":";
      json_buf_string buf name;
      Buffer.add_string buf ",\"ty\":";
      json_int buf ty;
      Buffer.add_string buf ",\"body\":";
      json_int buf body;
      Buffer.add_char buf '}'
    | TE_arrow { a; b } ->
      Buffer.add_string buf "{\"k\":\"arrow\",\"a\":";
      json_int buf a;
      Buffer.add_string buf ",\"b\":";
      json_int buf b;
      Buffer.add_char buf '}'
    | TE_eq { ty; l; r } ->
      Buffer.add_string buf "{\"k\":\"=\",\"ty\":";
      json_int buf ty;
      Buffer.add_string buf ",\"l\":";
      json_int buf l;
      Buffer.add_string buf ",\"r\":";
      json_int buf r;
      Buffer.add_char buf '}'
  in
  for i = 0 to n_exprs - 1 do
    emit_entry i (Vec.get entries i)
  done;
  for j = 0 to n_vars - 1 do
    emit_entry (n_exprs + j) (Vec.get var_entries j)
  done;
  ignore total;
  Buffer.add_char buf ']';

  (* Steps *)
  Buffer.add_string buf ",\"steps\":[";
  List.iteri
    (fun si (hyp_ids, concl_id, rule, parents, args) ->
      if si > 0 then Buffer.add_char buf ',';
      Buffer.add_string buf "{\"hyps\":[";
      List.iteri
        (fun j hid ->
          if j > 0 then Buffer.add_char buf ',';
          json_int buf hid)
        hyp_ids;
      Buffer.add_string buf "],\"concl\":";
      json_int buf concl_id;
      Buffer.add_string buf ",\"rule\":";
      json_buf_string buf rule;
      Buffer.add_string buf ",\"parents\":[";
      List.iteri
        (fun j p ->
          if j > 0 then Buffer.add_char buf ',';
          json_int buf p)
        parents;
      Buffer.add_string buf "],\"args\":[";
      List.iteri
        (fun j arg ->
          if j > 0 then Buffer.add_char buf ',';
          match arg with
          | `E eid ->
            Buffer.add_string buf "{\"e\":";
            json_int buf eid;
            Buffer.add_char buf '}'
          | `S ps ->
            Buffer.add_string buf "{\"s\":[";
            List.iteri
              (fun k (vid, eid) ->
                if k > 0 then Buffer.add_char buf ',';
                Buffer.add_char buf '[';
                json_int buf vid;
                Buffer.add_char buf ',';
                json_int buf eid;
                Buffer.add_char buf ']')
              ps;
            Buffer.add_string buf "]}")
        args;
      Buffer.add_string buf "]}")
    steps_arr;
  Buffer.add_string buf "]";

  Buffer.add_char buf '}';
  Buffer.contents buf

(* ---- h_proof_json handler ---- *)

let h_proof_json (self : state) : unit =
  H.add_route_handler self.server
    H.Route.(
      exact "proof-json" @/ string_urlencoded @/ string_urlencoded @/ return)
  @@ fun thy_name thm_idx_str req ->
  let@ () = top_wrap_ req in
  match int_of_string_opt thm_idx_str with
  | None ->
    H.Response.make_string
      (Error (400, spf "invalid theorem index: %s" thm_idx_str))
  | Some thm_idx ->
    let config = make_config_ self thy_name in
    let proofs_opt =
      let@ () = St.with_lock self.st.lock in
      (* Ensure the theory is loaded into the cache first, then load proofs *)
      (match self.st.zip with
      | None -> None
      | Some zh ->
        (match Proof_zip.load_theory zh ~ctx:self.st.ctx thy_name with
        | None -> None
        | Some _ -> Proof_zip.load_proofs zh ~ctx:self.st.ctx thy_name))
    in
    (match proofs_opt with
    | None ->
      H.Response.make_string
        (Error (404, spf "no proofs available for: %s" thy_name))
    | Some proofs ->
      (match List.nth_opt proofs thm_idx with
      | None ->
        H.Response.make_string
          (Error (404, spf "theorem index out of bounds: %d" thm_idx))
      | Some lp ->
        let json_str = proof_to_json lp config in
        let headers = [ "content-type", "application/json" ] in
        H.Response.make_string ~headers (Ok json_str)))

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
    let n_steps_opt =
      let@ () = St.with_lock self.st.lock in
      match self.st.zip with
      | None -> None
      | Some zh ->
        (match Proof_zip.load_proofs zh ~ctx:self.st.ctx thy_name with
        | None -> None
        | Some proofs ->
          (match List.nth_opt proofs thm_idx with
          | None -> None
          | Some lp -> Some (K.Linear_proof.steps lp |> Iter.length)))
    in
    let th_opt =
      let@ () = St.with_lock self.st.lock in
      St.load_theory self.st thy_name
    in
    (match th_opt, n_steps_opt with
    | None, _ ->
      H.Response.make_string (Error (404, spf "theory not found: %s" thy_name))
    | _, None ->
      H.Response.make_string
        (Error (404, spf "no proofs available for: %s" thy_name))
    | Some th, Some n_steps ->
      (match List.nth_opt (K.Theory.theorems th) thm_idx with
      | None ->
        H.Response.make_string
          (Error (404, spf "theorem index out of bounds: %d" thm_idx))
      | Some thm ->
        let config = make_config_ self thy_name in
        let type_offsets =
          match self.st.zip with
          | None -> None
          | Some zh -> Proof_zip.expr_offset_table zh thy_name
        in
        let open Html in
        let proof_url =
          spf "/proof-json/%s/%d" (H.Util.percent_encode thy_name) thm_idx
        in
        let res =
          [
            h3 [] [ txtf "Proof of theorem %d in %s" thm_idx thy_name ];
            div
              [ cls "mb-3" ]
              [
                strong [] [ txt "Theorem: " ];
                Render.thm_to_html ~config ?type_offsets ~entry:thy_name thm;
              ];
            div
              [
                A.id "proof-info";
                "data-proof-thy", H.Util.percent_encode thy_name;
                "data-proof-idx", string_of_int thm_idx;
              ]
              [];
            div
              [ A.id "proof-loading" ]
              [ txtf "Loading proof (%d steps)\xe2\x80\xa6" n_steps ];
            div
              [ A.id "proof-table"; A.style "display:none" ]
              [
                table
                  [ cls "table table-sm table-striped" ]
                  [
                    thead []
                      [
                        tr []
                          [
                            th [] [ txt "idx" ];
                            th [] [ txt "sequent" ];
                            th [] [ txt "rule" ];
                          ];
                      ];
                    tbody [ A.id "proof-tbody" ] [];
                  ];
              ];
            p [] [ txt "("; a [ A.href proof_url ] [ txt "raw JSON" ]; txt ")" ];
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

let create st ~port : state =
  let server = H.create ~addr:"127.0.0.1" ~port () in
  Tiny_httpd_camlzip.setup server;
  Tiny_httpd_prometheus.(instrument_server server global);
  let state = { server; st; port } in
  h_root state;
  h_thy state;
  h_art state;
  h_eval state;
  h_proof state;
  h_proof_json state;
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
