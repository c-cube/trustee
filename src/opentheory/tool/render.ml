
open Trustee_opentheory.Common_

module E = K.Expr

module Config = struct
  type t = {
    open_namespaces: string list;
  }

  let make ?(open_namespaces=[]) () : t =
    { open_namespaces }
end

let strip_name_ ~config (s:string) : string =
  match List.find (fun pre -> CCString.prefix ~pre s) config.Config.open_namespaces with
  | pre ->
    CCString.chop_prefix ~pre s |> Option.get_exn_or "strip name"
  | exception Not_found -> s

let is_a_binder c =
  match E.unfold_arrow @@ K.Const.ty c with
  | [a], _ret -> E.is_arrow a
  | _ -> false

let is_infix c name =
  let anum = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true | _ -> false in
  not (String.length name > 0 && anum name.[0]) &&
  match E.unfold_arrow @@ K.Const.ty c with
  | [_; _], _ -> true
  | _ -> false

let expr_to_html ?(config=Config.make()) (e:K.Expr.t) : Html.elt =
  let open Html in

  let rec loop k ~depth ~names e : Html.elt =
    let recurse = loop k ~depth ~names in
    let recurse' e = loop' k ~depth ~names e in
    match E.view e with
    | K.E_kind -> txt "kind"
    | K.E_type -> txt "type"
    | K.E_var v ->
      let name = K.Var.name v in
      let title_ = Fmt.asprintf "%s : %a" name E.pp (K.Var.ty v) in
      span [A.title title_] [txt name]
    | K.E_bound_var v ->

      let idx = v.bv_idx in
      let descr =
        match CCList.nth_opt names idx with
        | Some n when n<>"" -> n
        | _ ->
          if idx<k then spf "x_%d" (k-idx-1)
          else spf "%%db_%d" (idx-k)
      in
      let title_ = Fmt.asprintf "%s : %a" descr E.pp v.bv_ty in
      span [A.title title_] [txt descr]

    | K.E_const (c, []) ->
      let descr = strip_name_ ~config @@ K.Const.name c in
      let title_ =
        Fmt.asprintf "`%a`@ ty: %a" E.pp e E.pp (E.ty_exn e) in
      span [A.title title_] [txt descr]

    | K.E_const (c, args) when E.is_a_type e ->
      (* always write type arguments explicitly for types *)
      let descr = strip_name_ ~config @@ K.Const.name c in
      let title =
        Fmt.asprintf "`%a`@ ty: %a" E.pp e E.pp (E.ty_exn e) in
      span' [] [
        sub_e @@ span [A.title title] [txt descr];
        sub_l (
          CCList.flat_map
            (fun sub -> [txt " "; recurse' sub])
            args
        )
      ]

    | K.E_const (c, _) ->
      (* omit arguments *)
      let descr = strip_name_ ~config @@ K.Const.name c in
      let title =
        Fmt.asprintf "`%a`@ ty: %a" E.pp e E.pp (E.ty_exn e) in
      span [A.title title] [txt descr]

    | K.E_app (_, _) ->
      let f, args = E.unfold_app e in

      let default() =
        span' [][
          sub_e @@ recurse' f;
          sub_l (
            CCList.flat_map
              (fun sub -> [txt " "; recurse' sub])
              args
          )
        ]
      in

      begin match E.view f, args with
        | E_const (c, [_]), [a;b] when String.equal (K.Const.name c) "=" ->
          span[] [
            recurse' a;
            txt " = ";
            recurse' b
          ]

        | E_const (c, _), [lam] when E.is_lam lam && is_a_binder c ->
          (* shortcut display for binders *)
          let n, ty, bod = match E.view lam with
            | E_lam (n,ty,bod) -> n, ty, bod
            | _ -> assert false
          in
          let varname = if n="" then spf "x_%d" k else n in
          let vartitle = Fmt.asprintf "%s : %a" varname E.pp ty in
          let c_name = strip_name_ ~config @@ K.Const.name c in
          let c_title =
            Fmt.asprintf "`%a`@ ty: %a" E.pp f E.pp (E.ty_exn f) in
          span[] [
            span [A.title c_title] [txt c_name];
            span [A.title vartitle] [txt varname];
            txt ". ";
            loop (k+1) ~depth:(depth+1) ~names:(n::names) bod
          ]

        | E_const (c, _), [a; b] ->
          let c_name = strip_name_ ~config @@ K.Const.name c in
          if is_infix c c_name then (
            (* display infix *)
            let c_title =
              Fmt.asprintf "`%a`@ ty: %a" E.pp f E.pp (E.ty_exn f) in
            span[] [
              recurse' a;
              span [A.title c_title] [txt (spf " %s " c_name)];
              recurse' b
            ]
          ) else default()

        | _ -> default()
      end

    | E_lam (n, ty, bod) ->
      let varname = if n="" then spf "x_%d" k else n in
      let vartitle = Fmt.asprintf "%s : %a" varname E.pp ty in
      span[] [
        txt "λ";
        span [A.title vartitle] [txt varname];
        txt ". ";
        loop (k+1) ~depth:(depth+1) ~names:(n::names) bod
      ]

    | K.E_arrow (a, b) ->
      span[] [
        recurse' a;
        txt " -> ";
        recurse b
      ]

    | K.E_box _seq ->
      span[cls "box"][txtf "%a" E.pp e]

  and loop' k ~depth ~names e : Html.elt =
    match E.view e with
    | E_kind | E_type | E_var _ | E_bound_var _ | E_const _ | E_box _ ->
      loop k ~depth ~names e (* atomic expr *)
    | E_app _  | E_lam _ | E_arrow _ ->
      span[][txt "("; loop k ~depth ~names e; txt ")"]
  in
  span [cls "expr"] [loop 0 ~depth:0 ~names:[] e]

let const_to_html ?(config=Config.make ()) (c:K.Const.t) =
  let name = strip_name_ ~config @@ K.Const.name c in
  let args = Fmt.to_string K.Const.pp_args (K.Const.args c) in
  let title_ = Fmt.to_string K.Const.pp_with_ty c in
  Html.(
    span [cls "const"] [
      span [A.title title_] [txt name]; txt " "; txt args;
      txt " : "; expr_to_html ~config (K.Const.ty c)
    ]
  )

let thm_to_html ?(config=Config.make()) thm : Html.elt =
  let open Html in
  let hyps = K.Thm.hyps_l thm in
  let concl = K.Thm.concl thm in
  let bod =
    match hyps with
    | [] -> [txt "⊢"; expr_to_html ~config concl]
    | l ->
      (* TODO: some basic layout *)
      List.map (expr_to_html ~config) l @ [txt "⊢"; expr_to_html ~config concl]
  in
  span[cls "theorem"] bod

let subst_to_html su =
  Html.(pre[][txtf "%a" K.Subst.pp su])

let theory_to_html ?(config=Config.make()) (self:K.Theory.t) =
  let _name = K.Theory.name self in
  let in_consts = K.Theory.param_consts self in
  let in_thms = K.Theory.param_theorems self in
  let out_consts = K.Theory.consts self in
  let out_thms = K.Theory.theorems self in

  let open Html in
  div[cls "theory"][
    table'[cls "table table-sm table-striped table-bordered"] [
      sub_l (
        List.map
          (fun c ->
             tr[][
               td[cls "theory-param"][txt "in-const"];
               td[][const_to_html ~config c]
             ])
          in_consts
      );
      sub_l (
        List.map
          (fun th ->
             tr[][
               td[cls "theory-param"][txt "in-theorem"];
               td[][thm_to_html ~config th]
             ])
          in_thms
      );
      sub_l (
        List.map
          (fun c ->
             tr[][
               td[cls "theory-out"][txt "defined-const"];
               td[][const_to_html ~config c]
             ])
          out_consts
      );
      sub_l (
        List.map
          (fun th ->
             tr[][
               td[cls "theory-out"][txt "defined-theorem"];
               td[][thm_to_html ~config th]
             ])
          out_thms
      );
    ]
  ]
