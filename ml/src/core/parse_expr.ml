
open Sigs

module K = Kernel
module P = Parser_comb


open P.Infix

type position = Position.t lazy_t
module Ast = struct
  type ty = {
    ty_pos: position;
    ty_view: ty_view;
  }

  and ty_view =
    | Ty_arrow of ty * ty
    | Ty_var of string

  type t = {
    pos: position;
    view: view;
  }

  and var = {
    v_name: string;
    v_ty: ty option;
    v_kind: var_kind
  }

  and var_kind =
    | V_normal
    | V_at
    | V_question_mark

  and binding = var * t

  and view =
    | Var of var
    | Const of K.const
    | App of t * t list
    | Lambda of var list * t
    | Pi of string list * t
    | With of var list * t
    | Eq of t * t
    | Let of binding list * t

  let nopos: position = lazy Position.none
  let ty_pos ty = Lazy.force ty.ty_pos
  let pos e = Lazy.force e.pos

  let mk_var ?kind:(v_kind=V_normal) v_name v_ty : var = {v_name; v_ty; v_kind}

  let mk_ty_ ?(pos=nopos) ty_view : ty = { ty_view; ty_pos=pos; }
  let ty_var ?pos (s:string) : ty = mk_ty_ ?pos (Ty_var s)
  let ty_arrow ?pos a b : ty = mk_ty_ ?pos (Ty_arrow (a,b))

  let mk_ ?(pos=nopos) view : t = {view; pos}
  let var ?pos (v:var) : t = mk_ ?pos (Var v)
  let const ?pos c : t = mk_ ?pos (Const c)
  let app ?pos (f:t) (l:t list) : t = mk_ ?pos (App (f,l))
  let let_ ?pos bs bod : t = mk_ ?pos (Let (bs, bod))
  let with_ ?pos vs bod : t = mk_ ?pos (With (vs, bod))

  let pp_ty out ty : unit =
    let rec aux in_arrow out ty =
      match ty.ty_view with
      | Ty_var v -> Fmt.string out v
      | Ty_arrow (a,b) ->
        if in_arrow then Fmt.fprintf out "(@[";
        Fmt.fprintf out "%a@ -> %a" (aux true) a (aux in_arrow) b;
        if in_arrow then Fmt.fprintf out "@])";
    in
    aux false out ty

  let rec pp out (e:t) : unit =
    match e.view with
    | Var v -> Fmt.string out v.v_name
    | Const c -> K.Const.pp out c
    | App (f,l) -> Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_list pp) l
    | Lambda _ -> assert false (* TODO *)
    | Pi _ -> assert false (* TODO *)
    | With _ -> assert false (* TODO *)
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Let _ -> assert false (* TODO *)
end

type expr = Ast.t
type prec = int

let max_prec: prec = 1024

let skip_w = P.skip_white
let ident = P.ident
let keyword = P.keyword

let ty : Ast.ty P.t =
  P.fix @@ fun self ->
  let atomic_ty =
    skip_w *>
    P.if_ (P.char_exact '(')
      (fun _ -> self <* skip_w <* P.char_exact ')')
      begin
        (P.cur_pos <**> ident) >|= fun (pos,a) ->
        Ast.ty_var a ~pos
      end
  in
  (atomic_ty <* skip_w) >>= fun lhs ->
  P.if_ (keyword "->")
    (fun _ -> self >|= fun rhs -> Ast.ty_arrow lhs rhs)
    (P.return lhs)

let p_var_ : Ast.var P.t =
  skip_w *>
  ident >>= fun name ->
  skip_w *>
  begin
    P.if_ (P.char_exact ':')
      (fun _ -> skip_w *> ty >|= fun ty -> Ast.mk_var name (Some ty))
      (P.return (Ast.mk_var name None))
  end

let p_var_binding_ pexpr : Ast.binding P.t =
  skip_w *>
  p_var_ >>= fun v ->
  skip_w *>
  P.char_exact '=' *>
  skip_w *>
  pexpr >|= fun e ->
  v,e

let rec p_expr_ ctx (p:prec) : expr P.t =
  let op =
    (* operator with fixity *)
    ident >>= fun id ->
    begin match K.Ctx.find_const_by_name ctx id with
      | None -> P.fail "expected operator"
      | Some c ->
        let fix = K.Const.fixity c in
        P.return (c, fix, K.Fixity.get_prec fix)
    end
  in

  let atomic_expr : expr P.t =
    skip_w *>
    P.cond [
      begin
        (* maximum precedence *)
        P.ignore (P.char_exact '('),
        begin
          p_expr_ ctx max_prec <* skip_w <* P.char_exact ')'
        end
      end;
      begin
        P.ignore (P.char_exact '@'),
        begin
          ident >|= fun id -> Ast.var (Ast.mk_var ~kind:Ast.V_at id None)
        end
      end;
      begin
        P.ignore (P.char_exact '?'),
        begin
          ident >|= fun id -> Ast.var (Ast.mk_var ~kind:Ast.V_question_mark id None)
        end
      end;
      begin
        (* let binding *)
        P.ignore (keyword "let"),
        begin
          P.cur_pos >>= fun pos ->
          let pbinding = p_var_binding_ (p_expr_ ctx max_prec) in
          P.sep1 ~by:(skip_w *> keyword "and") pbinding
          >>= fun bs ->
          skip_w *> keyword "in" *>
          p_expr_ ctx p >|= fun body ->
          Ast.let_ ~pos bs body
        end
      end;
      begin
        (* beginning of an identifier *)
        P.ignore (P.lookahead (P.char_if P.is_alpha)),
        (P.cur_pos <**> p_var_) >|= fun (pos,v) -> Ast.var ~pos v
      end;
    ] (P.fail "expected expr")
  in
  P.cur_pos >>= fun pos ->
  atomic_expr >>= fun lhs ->
  begin
    begin
      (* left-assoc *)
      begin
        let lassoc = function
          | (_, K.F_left_assoc p2, _) -> p2 >= p
          | _ -> false
        in
        P.guard lassoc op
      end,
      fun (op, _, p2) ->
        p_expr_ ctx p2 >|= fun rhs ->
        Ast.app ~pos (Ast.const op) [lhs; rhs]
    end
    <||>
    (P.return lhs)
  end

let expr (ctx:K.Ctx.t) : _ P.t = p_expr_ ctx max_prec

let ty_eof = ty <* skip_w <* P.eoi
let expr_eof ctx = expr ctx <* skip_w <* P.eoi

(*$inject
  open Sigs
  let ctx = K.Ctx.create()

  let parse_print_ty s1 s2 =
    let x = P.parse_exn ty_eof s1 in
    let s1' = Fmt.asprintf "@[<h>%a@]" Ast.pp_ty x in
    (if s1' <> s2 then Printf.printf "s1=%S, s2=%S\n%!" s1' s2);
    s1' = s2

  let parse_print_expr s1 s2 =
    let x = P.parse_exn (expr_eof ctx) s1 in
    let s1' = Fmt.asprintf "@[<h>%a@]" Ast.pp x in
    (if s1' <> s2 then Printf.printf "s1=%S, s2=%S\n%!" s1' s2);
    s1' = s2
*)

(*$T
  parse_print_ty "a -> (b -> c)" "a -> b -> c"
  parse_print_ty "a -> b -> c" "a -> b -> c"
  parse_print_ty "(a -> b) -> c" "(a -> b) -> c"
  let ty = P.parse_exn ty_eof "  a" in (Ast.ty_pos ty).col = 3
*)
