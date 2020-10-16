
open Sigs

module K = Kernel
module P = Parser_comb

open P.Infix

module Ast = Parse_ast

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
  (* TODO
  P.if_ (keyword "pi")
    (fun _ ->
    )
     *)
    begin
      (atomic_ty <* skip_w) >>= fun lhs ->
      P.if_ (keyword "->")
        (fun _ -> self >|= fun rhs -> Ast.ty_arrow lhs rhs)
        (P.return lhs)
    end

let p_var_ : Ast.var P.t =
  skip_w *>
  ident >>= fun name ->
  skip_w *>
  begin
    P.if_ (P.char_exact ':')
      (fun _ -> skip_w *> ty >|= fun ty -> Ast.Var.make name (Some ty))
      (P.return (Ast.Var.make name None))
  end

let p_var_binding_ pexpr : Ast.binding P.t =
  skip_w *>
  p_var_ >>= fun v ->
  skip_w *>
  P.char_exact '=' *>
  skip_w *>
  pexpr >|= fun e ->
  v,e

(* right assoc *)
let (@||) = P.(<||>)

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
          p_expr_ ctx 0 <* skip_w <* P.char_exact ')'
        end
      end;
      begin
        P.ignore (P.char_exact '@'),
        begin
          ident >|= fun id -> Ast.var (Ast.Var.make ~kind:Ast.V_at id None)
        end
      end;
      begin
        P.ignore (P.char_exact '?'),
        begin
          ident >|= fun id -> Ast.var
            (Ast.Var.make ~kind:Ast.V_question_mark id None)
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
          | (_, K.F_left_assoc p2, _) when p2 >= p -> true
          | _ -> false
        in
        P.guard lassoc op
      end,
      fun (op, _, p2) ->
        p_expr_ ctx (p2+1) >|= fun rhs ->
        Ast.app ~pos (Ast.const (K.Expr.const ctx op)) [lhs; rhs]
    end
    @||
    begin
      (* left-assoc *)
      begin
        let rassoc = function
          | (_, K.F_right_assoc p2, _) when p2 >= p -> true
          | _ -> false
        in
        P.guard rassoc op
      end,
      fun (op, _, p2) ->
        p_expr_ ctx p2 >|= fun rhs ->
        Ast.app ~pos (Ast.const (K.Expr.const ctx op)) [lhs; rhs]
    end
    @||
    (P.return lhs)
  end

let expr (ctx:K.Ctx.t) : _ P.t = p_expr_ ctx 0

let ty_eof = ty <* skip_w <* P.eoi
let expr_eof ctx = expr ctx <* skip_w <* P.eoi

(*$inject
  open Sigs
  let ctx = K.Ctx.create()

  let parse_print_ty s1 s2 =
    let x = P.parse_exn ty_eof s1 in
    let s1' = Fmt.asprintf "@[<h>%a@]" Ast.pp x in
    let s2' = "`" ^ s2 ^ "`" in
    (if s1' <> s2' then Printf.printf "s1=%S, s2=%S\n%!" s1' s2');
    s1' = s2'

  let parse_print_expr s1 s2 =
    let x = P.parse_exn (expr_eof ctx) s1 in
    let s1' = Fmt.asprintf "@[<h>%a@]" Ast.pp x in
    let s2' = "`" ^ s2 ^ "`" in
    (if s1' <> s2' then Printf.printf "s1=%S, s2=%S\n%!" s1' s2');
    s1' = s2'
*)

(*$T
  parse_print_ty "a -> (b -> c)" "a -> b -> c"
  parse_print_ty "a -> b -> c" "a -> b -> c"
  parse_print_ty "(a -> b) -> c" "(a -> b) -> c"
  let ty = P.parse_exn ty_eof "  a" in (Ast.pos ty).col = 3
*)

(* TODO
  parse_print_ty "pi a b. a -> b -> c" "pi a b. a -> b -> c"
 *)
