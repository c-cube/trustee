
(** {1 Expression parser} *)

open Common_
module A = Parse_ast
module LL = Local_loc

module P_state = struct
  type t = {
    notation: Notation.t;
    lex: Lexer.t;
    bindings: A.Expr.var Str_tbl.t;
  }

  let create (src: Lexer.t) ~notation : t =
    { lex=src;
      notation;
      bindings=Str_tbl.create 16;
    }

  let eat_p ~msg self ~f : Token.t * Loc.t =
    let t2, loc = Lexer.S.cur self.lex in
    if f t2 then (
      Lexer.S.consume self.lex;
      t2, loc
    ) else (
      Error.failf ~loc
        (fun k->k "unexpected token %a while parsing;@ %s"
            Token.pp t2 msg)
    )

  let eat_p' ~msg self ~f : unit =
    ignore (eat_p ~msg self ~f : Token.t * _)

  let eat_eq ~msg self (t:Token.t) : Loc.t =
    snd @@ eat_p ~msg self ~f:(Token.equal t)

  let eat_eq' ~msg self (t:Token.t) : unit =
    eat_p' ~msg self ~f:(Token.equal t)
end

type state = P_state.t
type 'a parser_ = state -> 'a

(* We follow a mix of:
   - https://en.wikipedia.org/wiki/Operator-precedence_parser
   - https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
*)
module P_expr : sig
  val expr : ?ty_expect:A.Expr.t -> A.Expr.t parser_
  val expr_atomic : ?ty_expect:A.Expr.t -> A.Expr.t parser_
  val expr_and_eof : A.Expr.t parser_
  val p_tyvars_until :
    f:(Token.t -> bool) -> state -> A.Expr.var list -> Token.t * Loc.t * A.Expr.var list
  val p_const : A.Const.t parser_
  val p_ident : state -> string * Loc.t
end = struct
  open P_state
  open Loc.Infix

  type precedence = Fixity.precedence
  type t = P_state.t

  let fixity_ (self:t) (s:string) : Fixity.t =
    let module F = Fixity in
    match s with
    | "->" -> F.rassoc 100
    | "with" -> F.binder 1
    | "\\" -> F.binder 50
    | "=" -> F.infix 150
    | _ -> Notation.find_name_or_default self.notation (Name.make s)

  (* parse an identifier *)
  let p_ident self : string * Loc.t =
    match Lexer.S.cur self.lex with
    | SYM s, loc ->
      Lexer.S.consume self.lex;
      s, loc
    | _, loc ->
      Error.fail ~loc "expected identifier"

  let p_const (self:t) : A.Const.t =
    let name, loc = p_ident self in
    A.Const.make ~loc (Name.make name)

  let expr_of_string_ (self:t) ~loc (s:string) : A.Expr.t =
    match Str_tbl.find self.bindings s with
    | u -> A.Expr.var ~loc u
    | exception Not_found -> A.Expr.var ~loc (A.Var.make ~loc s None)

  (* parse let bindings *)
  let rec p_bindings_ self : (A.Expr.var * A.Expr.t) list =
    let name, loc = p_ident self in
    let v = A.Var.make ~loc name None in
    eat_eq' self EQDEF ~msg:"`:=` in let binding";
    let e = p_expr_ ~ty_expect:None self 0 in
    eat_eq' self IN ~msg:"expect `in` after let binding";
    [v, e]

  and p_tyvar_grp_ self : A.Expr.var list =
    let rec loop names =
      match Lexer.S.cur self.lex with
      | SYM s, loc ->
        Lexer.S.consume self.lex;
        loop ((s,loc)::names)
      | COLON, _loc ->
        Lexer.S.consume self.lex;
        let ty = p_expr_ ~ty_expect:(Some A.Expr.type_) self 0 in
        List.rev_map (fun (v,loc) -> A.Var.make ~loc v (Some ty)) names
      | (RPAREN | DOT), _loc ->
        List.rev_map (fun (v,loc) -> A.Var.make ~loc v None) names
      | _, loc ->
        Error.fail ~loc"expected group of typed variables"
    in
    loop []

  (* parse typed variables until a token matching [f] is found.
     Return that last token along with the variables. *)
  and p_tyvars_until ~f self acc : Token.t * Loc.t * A.Expr.var list =
    let t, loc = Lexer.S.cur self.lex in
    if f t then (
      Lexer.S.consume self.lex;
      t, loc, List.rev acc
    ) else (
      match Lexer.S.cur self.lex with
      | LPAREN, _loc ->
        Lexer.S.consume self.lex;
        let l = p_tyvar_grp_ self in
        eat_eq' self ~msg:"group of typed variables" RPAREN;
        p_tyvars_until ~f self (List.rev_append l acc)
      | SYM _, loc ->
        let l = p_tyvar_grp_ self in
        let last, _ = eat_p self ~f ~msg:"`.` terminating list of bound variables" in
        last, loc, List.rev @@ List.rev_append l acc
      | _, loc ->
        Error.fail ~loc "expected list of (typed) variables"
    )

  and p_tyvars_and_dot self acc : A.Expr.var list =
    let _d, _loc, l =
      p_tyvars_until self acc ~f:(function DOT -> true | _ -> false)
    in
    l

  and p_nullary_ ~loc (self:t) (s:string) : A.Expr.t =
    Log.debugf 6 (fun k->k"nullary `%s` loc=%a" s Loc.pp loc);
    match Lexer.S.cur self.lex with
    | COLON, _ ->
      Lexer.S.consume self.lex;
      let ty = p_expr_ ~ty_expect:(Some A.Expr.type_) self 0 in
      let loc = A.Expr.loc ty ++ loc in
      A.Expr.var ~loc (A.Var.make ~loc s (Some ty))
    | _ ->
      if s<>"" then (
        expr_of_string_ ~loc self s
      ) else (
        Error.failf ~loc (fun k->k"unknown symbol `%s`" s)
      )

  and p_expr_atomic_ ~ty_expect (self:t) : A.Expr.t =
    let t, loc_t = Lexer.S.cur self.lex in
    match t with
    | ERROR c ->
      Error.failf ~loc:loc_t (fun k->k"invalid char '%c'" c)
    | LPAREN ->
      Lexer.S.consume self.lex;
      let e = p_expr_ ~ty_expect self 0 in
      eat_eq' self ~msg:"atomic expression" RPAREN;
      e
    | LET ->
      Lexer.S.consume self.lex;
      (* parse `let x = e in e2` *)
      Log.debugf 5 (fun k->k"parsing let");
      let bs = p_bindings_ self in
      eat_eq' self ~msg:"let binding body" IN;
      List.iter (fun (v,_) -> Str_tbl.add self.bindings v.A.Var.name v) bs;
      let bod = p_expr_ ~ty_expect self 0 in
      List.iter (fun (v,_) -> Str_tbl.remove self.bindings v.A.Var.name) bs;
      A.Expr.let_ ~loc:(loc_t ++ A.Expr.loc bod) bs bod
    | SYM s ->
      Lexer.S.consume self.lex;
      begin match fixity_ self s with
        | _ when fst (Lexer.S.cur self.lex) = RPAREN ->
          (* case: `(=)` or `(+)`: return the sybol *)
          p_nullary_ ~loc:loc_t self s
        | F_normal -> p_nullary_ ~loc:loc_t self s
        | F_prefix i ->
          (* TODO: parse a list? *)
          let arg = p_expr_ ~ty_expect:None self i in
          let lhs = expr_of_string_ ~loc:loc_t self s in
          A.Expr.app lhs [arg]
        | F_binder i ->
          let vars = p_tyvars_and_dot self [] in
          let body = p_expr_ ~ty_expect self i in
          let loc = loc_t ++ A.Expr.loc body in
          begin match s with
            | "\\" -> A.Expr.lambda ~loc vars body
            | "with" -> A.Expr.with_ ~loc vars body
            | _ ->
              let b = A.Const.make ~loc:loc_t (Name.make s) in
              A.Expr.bind ~loc b vars body
          end
        | (F_left_assoc _ | F_right_assoc _ | F_postfix _ | F_infix _) ->
          Error.failf ~loc:loc_t
            (fun k->k
                "unexpected infix operator `%s`@ \
                 while parsing atomic expression" s)
      end
    | WILDCARD ->
      Lexer.S.consume self.lex;
      A.Expr.wildcard ~loc:loc_t ()
    | QUESTION_MARK_STR s ->
      Lexer.S.consume self.lex;
      A.Expr.meta ~loc:loc_t s None
    | QUOTE_STR s ->
      Lexer.S.consume self.lex;
      A.Expr.ty_var ~loc:loc_t s
    | QUESTION_MARK -> Error.fail ~loc:loc_t "TODO: `?`"
      (* TODO: remove interpolation and use this for free variables instead?
      begin match self.q_args with
        | [] -> errorf (fun k->k"no interpolation arg at %a" Loc.pp loc_t)
        | t :: tl -> self.q_args <- tl; A.Expr.of_k_expr ~loc:loc_t t
      end
           *)
    | NUM _ ->
      Error.fail ~loc:loc_t "TODO: parse numbers" (* TODO *)
    | RPAREN | COLON | DOT | IN | EOF | QUOTED_STR _
    | EQDEF | COMMA ->
      Error.fail ~loc:loc_t "expected expression"

  and p_expr_app_ ~ty_expect self : A.Expr.t =
    let e = ref (p_expr_atomic_ ~ty_expect self) in
    let continue = ref true in
    while !continue do
      match Lexer.S.cur self.lex with
      | LPAREN, _ ->
        Lexer.S.consume self.lex;
        let e2 = p_expr_ self ~ty_expect:None 0 in
        eat_eq' self RPAREN ~msg:"expect `)` to close sub-expression";
        e := A.Expr.app !e [e2];
      | SYM s, loc_s when fixity_ self s = Fixity.F_normal ->
        Lexer.S.consume self.lex;
        let e2 = p_nullary_ ~loc:loc_s self s in
        e := A.Expr.app !e [e2];
      | _ -> continue := false;
    done;
    !e

  and p_expr_ ~ty_expect (self:t) (p:precedence) : A.Expr.t =
    let lhs = ref (p_expr_app_ ~ty_expect self) in
    Log.debugf 6 (fun k->k"lhs: `%a` loc=%a prec=%d" A.Expr.pp !lhs Loc.pp (A.Expr.loc !lhs) p);
    let p = ref p in
    let continue = ref true in
    while !continue do
      match Lexer.S.cur self.lex with
      | (EOF | EQDEF), _ -> continue := false
      | LPAREN, _ ->
        Lexer.S.consume self.lex;
        let e = p_expr_ ~ty_expect:None self 0 in
        eat_eq' self ~msg:"expression" RPAREN;
        lhs := A.Expr.app !lhs [e]
      | (RPAREN | WILDCARD | COLON | DOT | IN | COMMA | LET), _loc -> continue
        := false
      | (QUESTION_MARK | QUOTED_STR _ | QUOTE_STR _
        | QUESTION_MARK_STR _ | NUM _), _ ->
        let e = p_expr_atomic_ ~ty_expect:None self in
        lhs := A.Expr.app !lhs [e];
      | SYM s, loc_s ->
        Lexer.S.consume self.lex;
        let f = fixity_ self s in
        begin match f with
          | (F_left_assoc p' | F_right_assoc p' | F_infix p') when p' >= !p ->
            let rhs = ref (p_expr_app_ ~ty_expect:None self) in
            let continue2 = ref true in
            (* parse right-assoc series *)
            while !continue2 do
              match Lexer.S.cur self.lex with
              | SYM s2, loc_s2 ->
                begin match fixity_ self s2 with
                  | F_right_assoc p2 when p2 = p' ->
                    Lexer.S.consume self.lex;
                    let e = p_expr_ self ~ty_expect:None p2 in
                    rhs := (
                      if s2 = "->" then (
                        let loc = loc_s2 ++ A.Expr.loc e in
                        A.Expr.ty_arrow ~loc [!rhs] e
                      ) else (
                        let op2 = expr_of_string_ ~loc:loc_s2 self s2 in
                        A.Expr.app op2 [!rhs; e]
                      )
                    )
                  | _ -> continue2 := false
                end
              | _ -> continue2 := false
            done;
            lhs := (
              let loc = loc_s ++ A.Expr.loc !lhs ++ A.Expr.loc !rhs in
              if s = "->" then A.Expr.ty_arrow ~loc [!lhs] !rhs
              else if s = "=" then A.Expr.eq ~loc !lhs !rhs
              else (
                let op = expr_of_string_ ~loc:loc_s self s in
                A.Expr.app op [!lhs; !rhs]
              )
            )
          | F_normal ->
            let arg = p_nullary_ ~loc:loc_s self s in
            lhs := A.Expr.app !lhs [arg]
          | F_prefix _ | F_postfix _ | F_binder _ ->
            (* TODO: in case of prefix, we could just parse an appliation *)
            Error.fail ~loc:loc_s "expected infix operator"
          | F_left_assoc _ | F_right_assoc _ | F_infix _ ->
            (* lower precedence *)
            continue := false
        end
      | ERROR c, loc ->
        Error.failf ~loc (fun k->k "lexing error: unexpected char '%c'" c)
    done;
    !lhs

  let expr_atomic ?ty_expect self : A.Expr.t =
    p_expr_atomic_ ~ty_expect self

  let expr ?ty_expect (self:t) : A.Expr.t =
    p_expr_ ~ty_expect self 0

  (* main entry point for expressions *)
  let expr_and_eof (self:t) : A.Expr.t =
    let e = expr self in
    let last_tok, _loc = Lexer.S.cur self.lex in
    if last_tok <> EOF then (
      Error.failf ~loc:_loc
        (fun k->k"expected end of input after parsing expression, but got %a"
            Token.pp last_tok);
    );
    e
end

type 'a or_error = ('a, Loc.t * Error.t) result

let parse_expr ~notation lex : A.Expr.t or_error =
  let p = P_state.create ~notation lex in
  try
    Error.guard (Error.wrap "parsing expression") @@ fun () ->
    let e = P_expr.expr_and_eof p in
    Ok e
  with Error.E err ->
    (* best effort location *)
    let loc = match Error.loc err with
      | Some l -> l
      | None -> snd @@ Lexer.S.cur lex
    in
    Error (loc,err)

let expr_of_string ?loc_offset ?(file="<string>") ~notation s : A.Expr.t or_error =
  parse_expr ~notation (Lexer.create ?loc_offset ~file s)
