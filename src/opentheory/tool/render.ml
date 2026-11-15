open Trustee_opentheory.Common_
module E = K.Expr

module Config = struct
  type t = {
    open_namespaces: string list;
    open_all_namespaces: bool;
  }

  let make ?(open_namespaces = []) ?(open_all_namespaces = false) () : t =
    { open_namespaces; open_all_namespaces }
end

let strip_name_ ~config (s : string) : string =
  if config.Config.open_all_namespaces then (
    match List.rev (String.split_on_char '.' s) with
    | c :: _ -> c
    | [] -> s
  ) else (
    match
      List.find
        (fun pre -> CCString.prefix ~pre s)
        config.Config.open_namespaces
    with
    | pre -> CCString.chop_prefix ~pre s |> Option.get_exn_or "strip name"
    | exception Not_found -> s
  )

let is_symbol_ s =
  let anum = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
    | _ -> false
  in
  not (String.length s > 0 && anum s.[0])

let is_a_binder c c_name =
  is_symbol_ c_name
  &&
  match E.unfold_arrow @@ K.Const.ty c with
  | [ a ], _ret -> E.is_arrow a
  | _ -> false

let is_infix c c_name =
  is_symbol_ c_name
  &&
  match E.unfold_arrow @@ K.Const.ty c with
  | [ _; _ ], _ -> true
  | _ -> false

let expr_wrap_ f e =
  let open Html in
  match E.view e with
  | E_kind | E_type | E_var _ | E_bound_var _ | E_box _ | E_const (_, []) ->
    f e (* atomic expr *)
  | E_const _ when not (E.is_a_type e) -> f e
  | E_app _ | E_lam _ | E_arrow _ | E_const _ ->
    span [] [ txt "("; f e; txt ")" ]

let percent_encode s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '-' | '_' | '.' | '~' ->
        Buffer.add_char buf c
      | c -> Buffer.add_string buf (Printf.sprintf "%%%02X" (Char.code c)))
    s;
  Buffer.contents buf

let href_const c = spf "/c/%s" (percent_encode @@ K.Const.name c)

(** Static [title=] fallback for server-rendered expressions. [fallback] is a
    thunk evaluated only when the span is emitted. *)
let ty_attrs_ ~fallback = [ "title", fallback () ]

let var_to_html (v : K.Var.t) : Html.elt =
  let open Html in
  let name = K.Var.name v in
  let ty = K.Var.ty v in
  let attrs =
    ty_attrs_ ~fallback:(fun () -> Fmt.asprintf "%s : %a" name E.pp ty)
  in
  span attrs [ txt name ]

let expr_to_html ?(config = Config.make ()) (e : K.Expr.t) : Html.elt =
  let open Html in
  let ty_attrs _ty fallback = ty_attrs_ ~fallback in
  let rec loop k ~depth ~names e : Html.elt =
    let recurse = loop k ~depth ~names in
    let recurse' e = loop' k ~depth ~names e in
    match E.view e with
    | K.E_kind -> txt "kind"
    | K.E_type -> txt "type"
    | K.E_var v -> var_to_html v
    | K.E_bound_var v ->
      let idx = v.bv_idx in
      let descr =
        match CCList.nth_opt names idx with
        | Some n when n <> "" -> n
        | _ ->
          if idx < k then
            spf "x_%d" (k - idx - 1)
          else
            spf "%%db_%d" (idx - k)
      in
      let attrs =
        ty_attrs v.bv_ty (fun () -> Fmt.asprintf "%s : %a" descr E.pp v.bv_ty)
      in
      span attrs [ txt descr ]
    | K.E_const (c, []) ->
      let c_name = strip_name_ ~config @@ K.Const.name c in
      let ty = E.ty_exn e in
      let attrs =
        ty_attrs ty (fun () -> Fmt.asprintf "%a : %a" E.pp e E.pp ty)
      in
      let href = href_const c in
      let res = span attrs [ a [ A.href href; cls "const" ] [ txt c_name ] ] in
      if is_a_binder c c_name || is_infix c c_name then
        span [] [ txt "("; res; txt ")" ]
      else
        res
    | K.E_const (c, args) when E.is_a_type e ->
      (* always write type arguments explicitly for types *)
      let descr = strip_name_ ~config @@ K.Const.name c in
      let ty = E.ty_exn e in
      let attrs =
        ty_attrs ty (fun () -> Fmt.asprintf "%a : %a" E.pp e E.pp ty)
      in
      span' []
        [
          sub_e
          @@ span attrs
               [ a [ A.href (href_const c); cls "const" ] [ txt descr ] ];
          sub_l (CCList.flat_map (fun sub -> [ txt " "; recurse' sub ]) args);
        ]
    | K.E_const (c, _) ->
      (* omit arguments *)
      let c_name = strip_name_ ~config @@ K.Const.name c in
      let ty = E.ty_exn e in
      let attrs =
        ty_attrs ty (fun () -> Fmt.asprintf "%a : %a" E.pp e E.pp ty)
      in
      let res =
        span attrs [ a [ A.href (href_const c); cls "const" ] [ txt c_name ] ]
      in
      if is_a_binder c c_name || is_infix c c_name then
        span [] [ txt "("; res; txt ")" ]
      else
        res
    | K.E_app (_, _) ->
      let f, args = E.unfold_app e in

      let default () =
        span' []
          [
            sub_e @@ recurse' f;
            sub_l (CCList.flat_map (fun sub -> [ txt " "; recurse' sub ]) args);
          ]
      in

      let c_name =
        match E.view f with
        | E_const (c, _) -> strip_name_ ~config @@ K.Const.name c
        | _ -> ""
      in

      (match E.view f, args with
      | E_const (c, [ _ ]), [ a; b ] when String.equal (K.Const.name c) "=" ->
        span [] [ recurse' a; txt " = "; recurse' b ]
      | E_const (c, _), [ lam ] when E.is_lam lam && is_a_binder c c_name ->
        (* shortcut display for binders *)
        let n, ty, bod =
          match E.view lam with
          | E_lam (n, ty, bod) -> n, ty, bod
          | _ -> assert false
        in
        let varname =
          if n = "" then
            spf "x_%d" k
          else
            n
        in
        let f_ty = E.ty_exn f in
        let c_attrs =
          ty_attrs f_ty (fun () -> Fmt.asprintf "%a : %a" E.pp f E.pp f_ty)
        in
        let var_attrs =
          ty_attrs ty (fun () -> Fmt.asprintf "%s : %a" varname E.pp ty)
        in
        let c_href = href_const c in
        span []
          [
            span c_attrs [ a [ A.href c_href; cls "const" ] [ txt c_name ] ];
            span var_attrs [ txt varname ];
            txt ". ";
            loop (k + 1) ~depth:(depth + 1) ~names:(n :: names) bod;
          ]
      | E_const (c, _), [ a; b ] when is_infix c c_name ->
        (* display infix *)
        let f_ty = E.ty_exn f in
        let c_attrs =
          ty_attrs f_ty (fun () -> Fmt.asprintf "%a : %a" E.pp f E.pp f_ty)
        in
        span []
          [
            recurse' a;
            span c_attrs
              [
                Html.a
                  [ A.href (href_const c); cls "const" ]
                  [ txt (spf " %s " c_name) ];
              ];
            recurse' b;
          ]
      | _ -> default ())
    | E_lam (n, ty, bod) ->
      let varname =
        if n = "" then
          spf "x_%d" k
        else
          n
      in
      let var_attrs =
        ty_attrs ty (fun () -> Fmt.asprintf "%s : %a" varname E.pp ty)
      in
      span []
        [
          txt "λ";
          span var_attrs [ txt varname ];
          txt ". ";
          loop (k + 1) ~depth:(depth + 1) ~names:(n :: names) bod;
        ]
    | K.E_arrow (a, b) -> span [] [ recurse' a; txt " -> "; recurse b ]
    | K.E_box _seq ->
      let title_ = Fmt.asprintf "box %a" E.pp e in
      span [ cls "box"; A.title title_ ] [ txtf "%a" E.pp e ]
  and loop' k ~depth ~names e : Html.elt =
    expr_wrap_ (loop k ~depth ~names) e
  in
  span [ cls "expr" ] [ loop 0 ~depth:0 ~names:[] e ]

let island ~(kind : string) ~(blob : string) ~(off : int) : Html.elt =
  Html.raw_html
    (spf "<trustee-view kind=\"%s\" blob=\"%s\" off=\"%d\"></trustee-view>" kind
       blob off)

let const_def_to_html ?(config = Config.make ()) ctx (c : K.Const.t) =
  let open Html in
  match K.Const_def.approx_def @@ K.Const.get_def_exn ctx c with
  | `Def rhs -> p [] [ txt "defined as: "; expr_to_html ~config rhs ]
  | `Ty_def phi ->
    p [] [ txt "defined type with predicate: "; expr_to_html ~config phi ]
  (*| `Erased -> p[][txt "erased definition"]*)
  | `Param -> p [] [ txt "theory parameter" ]
  | `Other -> p [] [ txt "opaque" ]

let const_head_html ?(config = Config.make ()) (c : K.Const.t) : Html.elt =
  let name = strip_name_ ~config @@ K.Const.name c in
  let args = Fmt.to_string K.Const.pp_args (K.Const.args c) in
  Html.(
    span []
      [
        a [ cls "const"; A.href (href_const c) ] [ txt name ];
        txt " ";
        txt args;
        txt " : ";
      ])

let const_to_html ?(config = Config.make ()) (c : K.Const.t) =
  Html.(
    span
      [ cls "const" ]
      [ const_head_html ~config c; expr_to_html ~config (K.Const.ty c) ])

let thm_to_html ?(config = Config.make ()) thm : Html.elt =
  let open Html in
  let hyps = K.Thm.hyps_l thm in
  let concl = K.Thm.concl thm in
  let bod =
    let title_ =
      Fmt.asprintf "fully concrete: %B" (K.Thm.is_fully_concrete thm)
    in
    let vdash =
      if K.Thm.proof thm |> K.Proof.is_main then
        span [ cls "theorem"; A.title title_ ] [ txt "⊢" ]
      else
        txt "⊢"
    in
    match hyps with
    | [] -> [ vdash; expr_to_html ~config concl ]
    | l ->
      (* TODO: some basic layout *)
      List.map (expr_to_html ~config) l @ [ vdash; expr_to_html ~config concl ]
  in
  span [ cls "theorem" ] bod

let option_at (a : int option array) (i : int) : int option =
  if i >= 0 && i < Array.length a then
    a.(i)
  else
    None

let theory_to_html ?(config = Config.make ())
    ?(make_proof_link : (int -> string) option) ~(blob : string)
    ~(const_offsets : int option array) ~(seq_offsets : int option array)
    (self : K.Theory.t) =
  let in_consts = K.Theory.param_consts self in
  let in_thms = K.Theory.param_theorems self in
  let out_consts = K.Theory.consts self in
  let out_thms = K.Theory.theorems self in

  let open Html in
  let const_row i c =
    match option_at const_offsets i with
    | Some off ->
      span
        [ cls "const" ]
        [ const_head_html ~config c; island ~kind:"term" ~blob ~off ]
    | None -> const_to_html ~config c
  in
  let thm_row i th =
    match option_at seq_offsets i with
    | Some off -> island ~kind:"sequent" ~blob ~off
    | None -> thm_to_html ~config th
  in
  div
    [ cls "theory" ]
    [
      table'
        [ cls "table table-sm table-striped table-bordered" ]
        [
          sub_l
            (List.mapi
               (fun i c ->
                 tr []
                   [
                     td [ cls "theory-param" ] [ txt "in-const" ];
                     td [] [ const_row i c ];
                   ])
               in_consts);
          sub_l
            (List.mapi
               (fun i th ->
                 tr []
                   [
                     td [ cls "theory-param" ] [ txt "in-theorem" ];
                     td [] [ thm_row i th ];
                   ])
               in_thms);
          sub_l
            (List.mapi
               (fun i c ->
                 tr []
                   [
                     td [ cls "theory-out" ] [ txt "defined-const" ];
                     td [] [ const_row (List.length in_consts + i) c ];
                   ])
               out_consts);
          sub_l
            (List.mapi
               (fun i th ->
                 let row = thm_row (List.length in_thms + i) th in
                 let proof_link =
                   match make_proof_link with
                   | None -> txt ""
                   | Some f ->
                     a
                       [
                         A.href (f i);
                         cls "btn btn-sm btn-outline-secondary ms-2";
                       ]
                       [ txt "proof" ]
                 in
                 tr []
                   [
                     td [ cls "theory-out" ] [ txt "defined-theorem" ];
                     td [] [ row; proof_link ];
                   ])
               out_thms);
        ];
    ]
