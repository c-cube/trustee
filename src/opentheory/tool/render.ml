
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

let is_symbol_ s =
  let anum = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true | _ -> false in
  not (String.length s > 0 && anum s.[0])

let is_a_binder c c_name =
  is_symbol_ c_name &&
  match E.unfold_arrow @@ K.Const.ty c with
  | [a], _ret -> E.is_arrow a
  | _ -> false

let is_infix c c_name =
  is_symbol_ c_name &&
  match E.unfold_arrow @@ K.Const.ty c with
  | [_; _], _ -> true
  | _ -> false

let expr_wrap_ f e =
  let open Html in
  match E.view e with
  | E_kind | E_type | E_var _ | E_bound_var _ | E_box _ | E_const (_, []) ->
    f e (* atomic expr *)
  | E_const _ when not (E.is_a_type e) -> f e
  | E_app _  | E_lam _ | E_arrow _ | E_const _ ->
    span[][txt "("; f e; txt ")"]

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
      let title_ = Fmt.asprintf "%s : %a@ hash %a"
          name E.pp (K.Var.ty v) K.Cr_hash.pp (K.Expr.cr_hash e) in
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
      let c_name = strip_name_ ~config @@ K.Const.name c in
      let title_ =
        Fmt.asprintf "%a : %a@ hash %a" E.pp e E.pp (E.ty_exn e)
          K.Cr_hash.pp (K.Expr.cr_hash e)
      in
      let res = span [A.title title_] [txt c_name] in
      if is_a_binder c c_name || is_infix c c_name
      then span[][txt "("; res; txt")"]
      else res

    | K.E_const (c, args) when E.is_a_type e ->
      (* always write type arguments explicitly for types *)
      let descr = strip_name_ ~config @@ K.Const.name c in
      let title =
        Fmt.asprintf "%a : %a@ hash %a" E.pp e E.pp (E.ty_exn e)
          K.Cr_hash.pp (K.Expr.cr_hash e)
      in
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
      let c_name = strip_name_ ~config @@ K.Const.name c in
      let title =
        Fmt.asprintf "%a : %a@ hash %a" E.pp e E.pp (E.ty_exn e)
          K.Cr_hash.pp (K.Expr.cr_hash e)
      in
      let res = span [A.title title] [txt c_name] in
      if is_a_binder c c_name || is_infix c c_name
      then span[][txt "("; res; txt")"]
      else res

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

      let c_name = match E.view f with
        | E_const (c, _) ->
          strip_name_ ~config @@ K.Const.name c
        | _ -> ""
      in

      begin match E.view f, args with
        | E_const (c, [_]), [a;b] when String.equal (K.Const.name c) "=" ->
          span[] [
            recurse' a;
            txt " = ";
            recurse' b
          ]

        | E_const (c, _), [lam] when E.is_lam lam && is_a_binder c c_name ->
          (* shortcut display for binders *)
          let n, ty, bod = match E.view lam with
            | E_lam (n,ty,bod) -> n, ty, bod
            | _ -> assert false
          in
          let varname = if n="" then spf "x_%d" k else n in
          let vartitle = Fmt.asprintf "%s : %a" varname E.pp ty in
          let c_title =
            Fmt.asprintf "%a : %a" E.pp f E.pp (E.ty_exn f) in
          span[] [
            span [A.title c_title] [txt c_name];
            span [A.title vartitle] [txt varname];
            txt ". ";
            loop (k+1) ~depth:(depth+1) ~names:(n::names) bod
          ]

        | E_const (c, _), [a; b] when is_infix c c_name ->
          (* display infix *)
          let c_title =
            Fmt.asprintf "%a : %a" E.pp f E.pp (E.ty_exn f) in
          span[] [
            recurse' a;
            span [A.title c_title] [txt (spf " %s " c_name)];
            recurse' b
          ]

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
      let title_ = Fmt.asprintf "box@ hash %a" K.Cr_hash.pp (K.Expr.cr_hash e) in
      span[cls "box"; A.title title_][
        txtf "%a" E.pp e
      ]

  and loop' k ~depth ~names e : Html.elt =
    expr_wrap_ (loop k ~depth ~names) e
  in
  span [cls "expr"] [loop 0 ~depth:0 ~names:[] e]

let const_to_html ?(config=Config.make ()) (c:K.Const.t) =
  let name = strip_name_ ~config @@ K.Const.name c in
  let args = Fmt.to_string K.Const.pp_args (K.Const.args c) in
  let title_ = Fmt.asprintf "%a@ hash: %a" K.Const.pp_with_ty c
      K.Cr_hash.pp (K.Const.cr_hash c) in
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
    let title_ = Fmt.asprintf "hash %a;@ in theory: %B"
        K.Cr_hash.pp (K.Thm.cr_hash thm) (K.Thm.is_in_theory thm) in
    let vdash = span [A.title title_] [txt "⊢"] in
    match hyps with
    | [] -> [vdash; expr_to_html ~config concl]
    | l ->
      (* TODO: some basic layout *)
      List.map (expr_to_html ~config) l @ [vdash; expr_to_html ~config concl]
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
