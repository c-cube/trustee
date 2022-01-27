
(** {1 Expression parser} *)

open Common_

module A = Parse_ast
module LL = Local_loc
module P = Parser

open Loc.Infix
open P.Infix

let spf = Printf.sprintf

(* recover: skip to the next token satisfying [ok], without consuming it *)
let try_recover ~ok : Loc.t P.t =
  let* loc0 = P.loc in

  let rec loop d =
    P.switch_next @@ fun tok loc ->
    match tok with
    | EOF ->
      `keep, P.return (loc0++loc)
    | _ when d=0 && ok tok ->
      `keep, P.return (loc0++loc)
    | LBRACE | LPAREN | LBRACKET ->
      `consume, loop (d+1) (* keep track of nesting, kind of *)
    | RBRACE | RPAREN | RBRACKET -> `consume, loop (d-1)
    | _ ->
      `consume, loop d
  in

  loop 0

let try_recover_semi = try_recover ~ok:(Token.equal SEMI_COLON)
let try_recover_rbrace = try_recover ~ok:(Token.equal RBRACE)
let try_recover_semi_or_rbrace =
  try_recover ~ok:(function RBRACE | SEMI_COLON -> true | _ -> false)

let[@inline] m_ str () : string = str

(* parse like [p], but between "{" "}". Also returns the location of "}". *)
let in_braces ~what (p:'a P.t) : ('a * Loc.t) P.t =
  let* () = P.exact' LBRACE ~msg:(fun()->spf"expect `{` to open %s" what) in
  let* bl = p in
  let+ loc = P.exact RBRACE ~msg:(fun()->spf"expect closing `}` after %s" what) in
  bl, loc

(** parse a list of [p], until [stop] is met, separated by [sep]. *)
let list_many ~what ~sep ~stop p : _ list P.t =
  let rec loop acc =
    P.switch_next @@ fun tok _ ->
    if Token.equal tok stop then (
      `keep, P.return (List.rev acc)
    ) else (
      `keep,
      let* x = p in
      loop1 (x::acc)
    )
  and loop1 acc =
    P.switch_next @@ fun tok _ ->
    if Token.equal tok stop then (
      `keep, P.return (List.rev acc)
    ) else if Token.equal tok sep then (
      `consume,
      loop acc
    ) else (
      `keep,
      P.fail_strf "expected %a or %a after an element,@ in a list of %s"
        Token.pp sep Token.pp stop what
    ) in
  loop []


(* We follow a mix of:
   - https://en.wikipedia.org/wiki/Operator-precedence_parser
   - https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
*)
module P_expr : sig
  type bindings = A.Expr.var Str_map.t

  val p_tyvars_until :
    notation:Notation.t ->
    f:(Token.t -> bool) ->
    A.Expr.var list ->
    (Token.t * Loc.t * A.Expr.var list) Parser.t

  val p_const : A.Const.t Parser.t
  val p_ident : (string * Loc.t) Parser.t

  val expr :
    ?ty_expect:A.Expr.t ->
    ?bindings:bindings ->
    notation:Notation.t ->
    unit -> A.Expr.t Parser.t

  val expr_atomic :
    ?ty_expect:A.Expr.t ->
    ?bindings:bindings ->
    notation:Notation.t ->
    unit -> A.Expr.t Parser.t

  val expr_and_eof :
    notation:Notation.t ->
    unit ->
    A.Expr.t Parser.t
end = struct
  type bindings = A.Expr.var Str_map.t
  type precedence = Fixity.precedence

  let fixity_ ~notation (s:string) : Fixity.t =
    let module F = Fixity in
    match s with
    | "->" -> F.rassoc 100
    | "with" -> F.binder 1
    | "\\" -> F.binder 50
    | "=" -> F.infix 150
    | _ -> Notation.find_name_or_default notation (Name.make s)

  (* parse an identifier *)
  let p_ident : (string * Loc.t) P.t =
    let* tok, loc = P.next in
    match tok with
    | SYM s -> P.return (s, loc)
    | tok -> P.fail_strf "expected an identifier, got `%a`" Token.pp tok

  let p_const : A.Const.t P.t =
    let+ name, loc = p_ident in
    A.Const.make ~loc (Name.make name)

  (* parse a group of variables with the same type annotation (or lack thereof) *)
  let rec p_tyvar_grp_ ~notation () : A.Expr.var list P.t =
    let rec loop names =
      P.switch_next @@ fun tok loc ->
      match tok with
      | SYM s -> `consume, loop ((s,loc) :: names)
      | COLON ->
        let p =
          let+ ty =
            p_expr_ ~bindings:Str_map.empty ~notation
              ~ty_expect:(Some A.Expr.type_) 0 in
          List.rev_map (fun (v,loc) -> A.Var.make ~loc v (Some ty)) names
        in
        `consume, p
      | RPAREN | DOT ->
        let p =
          P.return @@
          List.rev_map (fun (v,loc) -> A.Var.make ~loc v None) names
        in
        `consume, p
      | _ ->
        `keep, P.fail_strf "expected group of typed variables"
    in
    loop []

  (* parse let bindings *)
  and p_bindings_ ~notation ~bindings () : (A.Expr.var * A.Expr.t) list P.t =
    let rec loop acc =
      let* name, loc = p_ident in
      let v = A.Var.make ~loc name None in
      let* () = P.exact' EQDEF ~msg:(m_"`:=` in let binding") in
      let* e = p_expr_ ~notation ~bindings ~ty_expect:None 0 in
      P.switch_next @@ fun tok _loc ->
      match tok with
      | IN -> `keep, P.return @@ List.rev ((v,e) :: acc)
      | AND ->
        `consume, loop ((v,e) :: acc)
      | _ ->
        `keep, P.fail_str "expected `in` or `and`"
    in
    loop []

  (* parse typed variables until a token matching [f] is found.
     Return that last token along with the variables. *)
  and p_tyvars_until ~notation ~f acc : (Token.t * Loc.t * A.Expr.var list) P.t =
    P.switch_next @@ fun tok loc ->
    if f tok then (
      `consume, P.return (tok, loc, List.rev acc)
    ) else (
      match tok with
      | LPAREN ->
        `consume,
        let* l = p_tyvar_grp_ ~notation () in
        let* () = P.exact' RPAREN ~msg:(m_"expect ')' after a group of typed variables") in
        p_tyvars_until ~notation ~f (List.rev_append l acc)
      | SYM _ ->
        `keep,
        let* l = p_tyvar_grp_ ~notation () in
        let+ last, _ = P.token_if f ~msg:(m_"`.` terminating list of bound variables") in
        last, loc, List.rev @@ List.rev_append l acc
      | _ ->
        `keep,
        P.fail_str "expected list of (typed) variables"
    )

  and p_tyvars_and_dot ~notation acc : A.Expr.var list P.t =
    let+ _d, _loc, l =
      p_tyvars_until ~notation acc ~f:(function DOT -> true | _ -> false)
    in
    l

  and find_var_in_bindings ~loc ~bindings s ty =
    match Str_map.find_opt s bindings with
    | None -> A.Var.make ~loc s ty
    | Some v2 -> v2

  and expr_of_var ~loc ~bindings s ty : A.Expr.t =
    let v = find_var_in_bindings ~loc ~bindings s ty in
    A.Expr.var ~loc v

  and p_nullary_ ~loc ~bindings ~notation (s:string) : A.Expr.t P.t =
    P.switch_next @@ fun tok loc ->
    match tok with
    | COLON ->
      `consume,
      let+ ty = p_expr_ ~bindings ~notation ~ty_expect:(Some A.Expr.type_) 0 in
      let loc = A.Expr.loc ty ++ loc in
      expr_of_var ~loc ~bindings s (Some ty)
    | _ ->
      `keep,
      if s<>"" then (
        P.return @@ expr_of_var ~loc ~bindings s None
      ) else (
        Error.failf ~loc (fun k->k"unknown symbol `%s`" s)
      )

  and p_expr_atomic_ ~bindings ~notation ~ty_expect () : A.Expr.t P.t =
    P.switch_next @@ fun tok loc_t ->
    match tok with
    | ERROR c ->
      `consume,
      P.fail (Error.makef "invalid char '%c'" c)
    | LPAREN ->
      `consume,
      let* e = p_expr_ ~notation ~bindings ~ty_expect 0 in
      let+ () = P.rparen ~msg:(m_"expected a closing ')' after an atomic expression") () in
      e
    | LET ->
      `consume,
      (* parse `let x = e in e2` *)
      let* bs = p_bindings_ ~notation ~bindings () in
      let* () = P.exact' IN ~msg:(m_"let binding body") in
      let bindings =
        List.fold_left
          (fun bs (v,_) -> Str_map.add v.A.Var.name v bs)
          bindings bs in
      let* bod = p_expr_ ~notation ~ty_expect ~bindings 0 in
      P.return @@ A.Expr.let_ ~loc:(loc_t ++ A.Expr.loc bod) bs bod
    | SYM s ->
      let name = Name.make s in
      begin match Notation.find_name_or_default notation name with
        (* FIXME
        | _ when fst (Lexer.S.cur self.lex) = RPAREN ->
          (* case: `(=)` or `(+)`: return the sybol *)
          p_nullary_ ~loc:loc_t self s
           *)
        | F_normal ->
          `consume,
          p_nullary_ ~notation ~loc:loc_t ~bindings s
        | F_prefix i ->
          (* TODO: parse a list? *)
          `consume,
          let+ arg = p_expr_ ~bindings ~notation ~ty_expect:None i in
          let lhs = expr_of_var ~loc:loc_t ~bindings s None in
          A.Expr.app lhs [arg]
        | F_binder i ->
          `consume,
          (
          Log.debug 0 "binder";
          let* vars = p_tyvars_and_dot ~notation [] in
          Log.debug 0 "parsed vars";
          let+ body = p_expr_ ~bindings ~notation ~ty_expect i in
          let loc = loc_t ++ A.Expr.loc body in
          begin match s with
            | "\\" -> A.Expr.lambda ~loc vars body
            | "with" -> A.Expr.with_ ~loc vars body
            | _ ->
              let b = A.Const.make ~loc:loc_t (Name.make s) in
              A.Expr.bind ~loc b vars body
          end)
        | (F_left_assoc _ | F_right_assoc _ | F_postfix _ | F_infix _) ->
          `keep,
          P.fail_strf
            "unexpected infix operator `%s`@ \
             while parsing atomic expression" s
      end
    | WILDCARD ->
      `consume,
      P.return @@ A.Expr.wildcard ~loc:loc_t ()
    | QUESTION_MARK_STR s ->
      `consume,
      P.return @@ A.Expr.meta ~loc:loc_t s None
    | QUOTE_STR s ->
      `consume,
      P.return @@ A.Expr.ty_var ~loc:loc_t s
    | QUESTION_MARK -> `keep, P.fail_str "TODO: `?`"
      (* TODO: remove interpolation and use this for free variables instead?
      begin match self.q_args with
        | [] -> errorf (fun k->k"no interpolation arg at %a" Loc.pp loc_t)
        | t :: tl -> self.q_args <- tl; A.Expr.of_k_expr ~loc:loc_t t
      end
           *)
    | NUM _ ->
      `keep,
      P.fail_str "TODO: parse numbers" (* TODO *)
    | RPAREN | COLON | DOT | IN | AND | EOF | QUOTED_STR _
    | LBRACE | RBRACE | EQDEF | SEMI_COLON | DOLLAR | IF | MATCH
    | COMMA | SINGLE_QUOTE | RBRACKET | LBRACKET | FAT_ARROW ->
      `keep, P.fail_str "expected expression"

  and p_expr_app_ ~bindings ~notation ~ty_expect () : A.Expr.t P.t =
    let rec loop e : A.Expr.t P.t =
      P.switch_next @@ fun tok loc_t ->
      match tok with
      | LPAREN ->
        `consume,
        let* e2 = p_expr_ ~notation ~bindings ~ty_expect:None 0 in
        let* () = P.rparen ~msg:(m_"expect `)` to close sub-expression") () in
        loop @@ A.Expr.app e [e2]

      | SYM s when Notation.find_name_or_default notation (Name.make s) = Fixity.F_normal ->
        `consume,
        let* e2 = p_nullary_ ~notation ~bindings ~loc:loc_t s in
        loop @@ A.Expr.app e [e2]

      | _ -> `keep, P.return e
    in

    (* parse left-most term *)
    let* e0 = p_expr_atomic_ ~ty_expect ~bindings ~notation () in
    loop e0

  and p_expr_ ~notation ~bindings ~ty_expect (p:precedence) : A.Expr.t P.t =
    let rec loop lhs p : A.Expr.t P.t =
      P.switch_next @@ fun tok loc_t ->
      match tok with
      | (EOF | LBRACE | RBRACE | RBRACKET | DOLLAR | EQDEF) ->
        `keep, P.return lhs

      | LPAREN ->
        `consume,
        let* e = p_expr_ ~bindings ~notation ~ty_expect:None 0 in
        let* () = P.rparen ~msg:(m_"closing `)` in expression") () in
        loop (A.Expr.app lhs [e]) p

      | (RPAREN | WILDCARD | COLON | DOT | IN | COMMA | SEMI_COLON
        | LET | AND | SINGLE_QUOTE| LBRACKET) ->
        `keep, P.return lhs

      | (QUESTION_MARK | QUOTED_STR _ | QUOTE_STR _
        | QUESTION_MARK_STR _ | NUM _) ->
        `keep,
        let* e = p_expr_atomic_ ~notation ~bindings ~ty_expect:None () in
        loop (A.Expr.app lhs [e]) p

      | SYM s ->
        `consume,
        let f = Notation.find_name_or_default notation (Name.make s) in
        begin match f with
          | (F_left_assoc p' | F_right_assoc p' | F_infix p') when p' >= p ->

            (* parse right-assoc series *)
            let rec loop2 rhs =
              P.switch_next @@ fun tok2 loc2 ->
              match tok2 with
              | SYM s2 ->
                begin match Notation.find_name_or_default notation (Name.make s2) with
                  | F_right_assoc p2 when p2 = p' ->
                    `consume,
                    let* e = p_expr_ ~notation ~bindings ~ty_expect:None p2 in
                    let rhs =
                      if s2 = "->" then (
                        let loc = loc2 ++ A.Expr.loc e in
                        A.Expr.ty_arrow ~loc rhs e
                      ) else (
                        let op2 = expr_of_var ~bindings ~loc:loc2 s2 None in
                        A.Expr.app op2 [rhs; e]
                      )
                    in
                    loop2 rhs

                  | _ ->
                    `keep, P.return rhs
                end

              | _ -> `keep, P.return rhs
            in

            let* rhs = p_expr_app_ ~notation ~bindings ~ty_expect:None () in
            let* rhs = loop2 rhs in

            let lhs =
              let loc = loc_t ++ A.Expr.loc lhs ++ A.Expr.loc rhs in
              if s = "->" then A.Expr.ty_arrow ~loc lhs rhs
              else if s = "=" then A.Expr.eq ~loc lhs rhs
              else (
                let op = expr_of_var ~bindings ~loc:loc_t s None in
                A.Expr.app op [lhs; rhs]
              )
            in
            loop lhs p

          | F_normal ->
            let* arg = p_nullary_ ~notation ~bindings ~loc:loc_t s in
            let lhs = A.Expr.app lhs [arg] in
            loop lhs p

          | F_prefix _ | F_postfix _ | F_binder _ ->
            (* TODO: in case of prefix, we could just parse an appliation *)
            P.fail (Error.make ~loc:loc_t "expected infix operator")

          | F_left_assoc _ | F_right_assoc _ | F_infix _ ->
            (* lower precedence *)
            P.return lhs
        end

      | IF | MATCH | FAT_ARROW ->
        `consume,
        P.fail (Error.make ~loc:loc_t "expected expression")
      | ERROR c ->
        `keep,
        P.fail_strf "lexing error: unexpected char %C" c
    in

    let* lhs0 = p_expr_app_ ~bindings ~notation ~ty_expect () in
    loop lhs0 p

  let expr_atomic ?ty_expect ?(bindings=Str_map.empty) ~notation () : A.Expr.t P.t =
    p_expr_atomic_ ~ty_expect ~bindings ~notation ()

  let expr ?ty_expect ?(bindings=Str_map.empty) ~notation () : A.Expr.t P.t =
    p_expr_ ~ty_expect ~bindings ~notation 0

  (* main entry point for expressions *)
  let expr_and_eof ~notation () : A.Expr.t P.t =
    let* e = expr ~notation () in
    let* () = P.eoi ~msg:(m_"expected end of input after expression") () in
    P.return e
end

module P_subst : sig
  val subst :
    notation:Notation.t ->
    unit -> A.Subst.t P.t
end = struct
  let subst ~notation () : _ P.t =
    let* loc1 = P.loc in
    let rec p_binding ~expect_comma s : A.Subst.t P.t =
      P.switch_next @@ fun tok loc_t ->
      match tok with
      | RBRACE ->
        `consume,
        P.return @@ A.Subst.mk_ ~loc:(loc1 ++ loc_t) (List.rev s)

      | COMMA when expect_comma ->
        `consume,
        p_binding ~expect_comma:false s

      | _ ->
        `keep,
        if expect_comma then (
          P.fail_str "expected `,` or `}` after a substitution binding"
        ) else (
          let* v, loc_v = P_expr.p_ident in
          let* () = P.exact' EQDEF ~msg:(m_"expect `:=` in substitution") in
          let* e = P_expr.expr ~notation () in
          let s = ({A.view=v;loc=loc_v},e)::s in
          p_binding ~expect_comma:true s
        )
    in
    let* () = P.exact' (SYM "subst") ~msg:(m_"expect `subst`") in
    let* () = P.exact' LBRACE ~msg:(m_"expect opening `{` after `subst`") in
    p_binding ~expect_comma:false []
end

module P_meta_expr : sig
  val meta_expr :
    notation:Notation.t ->
    unit ->
    A.Meta_expr.t P.t
end = struct
  module E = A.Meta_expr

  let p_var = P_expr.p_ident

  let rec meta_expr_rec_ ~notation () : _ P.t =
    P.switch_next @@ fun tok t_loc ->
    begin match tok with
      | NUM n ->
        (* TODO: handle int parsing error *)
        `consume,
        P.return @@ E.mk ~loc:t_loc (E.Value (E.V_int (int_of_string n)))

      | SYM (("true" | "false") as b) ->
        `consume,
        P.return @@ E.mk ~loc:t_loc (E.Value (E.V_bool (bool_of_string b)))

      | QUOTED_STR s ->
        `consume,
        P.return @@ E.mk ~loc:t_loc (E.Value (E.V_string s))

      | LBRACE ->
        (* parse a block *)
        `consume,
        let* bl, loc = block_stmts ~notation [] in
        P.return @@ E.mk ~loc (E.Block_expr bl)

      | LBRACKET ->
        `consume,
        (* TODO: comprehensions *)
        let* l =
          list_many ~what:"meta-expressions" ~sep:COMMA ~stop:RBRACKET @@
          meta_expr_rec_ ~notation () in
        let* loc2 =
          P.exact RBRACKET ~msg:(m_"expect closing `]` after list literal") in
        let loc = t_loc ++ loc2 in
        P.return @@ E.mk ~loc (E.List_lit l)

      | DOLLAR ->
        `consume,
        let* e = P_expr.expr ~notation () in
        let+ loc2 = P.exact DOLLAR ~msg:(m_ "expect closing `$` after expression") in
        let loc = t_loc ++ loc2 in
        E.mk ~loc (E.Expr_lit e)

      | IF ->
        `consume,
        assert false

      | MATCH ->
        `consume,
        assert false

      | SYM c ->
        `consume,
        P.switch_next @@ fun tok2 loc2 ->
        begin match tok2 with
          | SINGLE_QUOTE ->
            (* c'accessor *)
            `consume,
            let* accessor = P_expr.p_const in
            let+ loc2 = P.loc in
            let loc = t_loc ++ loc2 in
            E.mk ~loc (E.Const_accessor (A.Const.make_str ~loc:t_loc c, accessor))

          | _ ->
            (* variable, application, or infix expression*)
            `keep,
            let lhs = E.mk ~loc:t_loc (E.Var (A.Var.make ~loc:t_loc c None)) in
            meta_expr_apply_ ~notation lhs
        end

      | LPAREN ->
        `consume,
        P.switch_next @@ fun tok2 loc2 ->
        begin match tok2 with
          | RPAREN ->
            `consume,
            P.return @@ E.mk ~loc:t_loc (E.Value (E.V_unit))

          | _ ->
            (* parse sub-expression *)
            `keep,
            let* e = meta_expr_rec_ ~notation () in
            let+ () = P.exact' RPAREN ~msg:(m_"expect closing `)` after expression") in
            e

        end

      | ERROR c ->
        (* lexer error *)
        `consume,
        let err = Error.makef ~loc:t_loc "expected meta-expression, not %C" c in
        P.return @@ E.mk ~loc:t_loc (E.Error err)

      | EQDEF | IN | AND | WILDCARD | SINGLE_QUOTE | DOT | RBRACKET
      | COMMA | SEMI_COLON | RPAREN | QUESTION_MARK | QUOTE_STR _
      | QUESTION_MARK_STR _ | RBRACE | COLON | EOF | LET | FAT_ARROW ->
        `keep,
        P.fail_str "expected meta-expression"
    end

  and meta_expr_apply_ ~notation lhs : E.t P.t =
    P.switch_next @@ fun tok t_loc ->
    match tok with
    | RPAREN | RBRACKET | RBRACE | SEMI_COLON ->
      `keep,
      P.return lhs

    | LPAREN | LBRACKET | LBRACE ->
      `keep,
      let* e = meta_expr_rec_ ~notation () in
      let lhs = E.apply lhs [e] in
      meta_expr_apply_ ~notation lhs

    | SYM "+" ->
      assert false

    | SYM s ->
      (* TODO: make var, apply *)
      assert false

    | _ -> assert false (* TODO: fail? *)

  and block_stmt ~notation () : (E.block_stmt * [`last | `any]) P.t =
    P.parsing (Error.wrap "parsing a block statement") @@
    P.switch_next @@ fun tok loc ->
    match tok with
    | RBRACE ->
      `keep, P.fail_str "expected statement"
    | LET ->
      `consume,
      let* x, x_loc = p_var in
      let x = A.Var.make ~loc:x_loc x None in
      let* () = P.exact' EQDEF ~msg:(m_"expect `:=` in let binding") in
      let* e = meta_expr_rec_ ~notation () in
      let* loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after let binding") in

      let stmt = E.mk_bl ~loc:(loc++loc2) @@ E.Blk_let (x,e) in
      P.return (stmt, `any)

    | SYM "return" ->
      `consume,
      let* e = meta_expr_rec_ ~notation () in
      let* loc3 = P.exact SEMI_COLON ~msg:(m_"expect `;` after `return <expr>`") in
      let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_return e in
      P.return (stmt, `last)

    | IF ->
      `consume,
      let* test = meta_expr_rec_ ~notation () in
      let* (then_,_), loc1 = in_braces ~what:"if branch" @@ block_stmts ~notation [] in

      let rec p_rest elseifs loc =
        P.switch_next @@ fun tok2 loc2 ->
        match tok2 with
        | SYM "else" ->
          `consume,
          P.switch_next @@ fun tok3 _ ->
          if Token.equal tok3 IF then (
            (* a "else if" *)
            `consume,
            let* cond = meta_expr_rec_ ~notation () in
            let* (bl,_), loc =
              in_braces ~what:"else if branch" @@ block_stmts ~notation [] in
            p_rest ((cond,bl)::elseifs) loc
          ) else (
            `keep,
            (* a real "else" *)
            let* (bl,_), loc =
              in_braces ~what:"else branch" @@ block_stmts ~notation [] in
            P.return (List.rev elseifs, Some bl, loc)
          )
        | _ ->
          `keep,
          P.return (List.rev elseifs, None, loc)
      in

      let* else_ifs, else_, loc2 = p_rest [] loc1 in
      let loc = loc ++ loc2 in
      let stmt = E.mk_bl ~loc @@ E.Blk_if {test; then_; else_ifs; else_} in
      P.return (stmt, `any)

    | _ ->
      (* parse either [e] or [e;] *)
      `keep,
      let* e = meta_expr_rec_ ~notation () in
      begin
        P.switch_next @@ fun tok3 loc3 ->
        match tok3 with
        | SEMI_COLON ->
          `consume,
          let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_eval_seq e in
          P.return (stmt, `any)

        | _ ->
          `keep,
          let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_eval e in
          P.return (stmt, `last)
      end

  (* read a block, return the `}`'s location *)
  and block_stmts ~notation acc : (E.block_expr * Loc.t) P.t =
    P.switch_next @@ fun tok loc ->
    match tok with
    | RBRACE ->
      `consume,
      let bl = {E.stmts=List.rev acc} in
      P.return (bl, loc)

    | _ ->
      `keep,
      let* st, islast =
        let* r = P.try_ @@ block_stmt ~notation () in
        match r with
        | Ok x -> P.return x
        | Error err ->
          (* catch errors and wrap them *)

          let* () = (* make sure to make progress *)
            let* loc2 = P.loc in
            if Loc.same_local_loc loc loc2
            then let+ _ = P.next in () else P.return () in (* skip *)

          let* loc = try_recover_semi_or_rbrace in
          let bl = E.mk_bl ~loc @@ E.Blk_error err in
          P.return (bl, `any)
      in
      begin match islast with
        | `last ->
          let bl = {E.stmts=List.rev acc} in
          P.return (bl, loc)
        | `any ->
          block_stmts ~notation (st::acc)
      end

  let meta_expr ~notation () : A.Meta_expr.t P.t =
    P.parsing (Error.wrap "parsing meta-expression") @@
    meta_expr_rec_ ~notation ()
end

module P_goal : sig
  val goal : notation:Notation.t -> unit -> A.Goal.t Parser.t
end = struct
  (* parse a sequent *)
  let goal ~notation () : A.Goal.t P.t =
    let* loc1 = P.loc in
    let* e = P_expr.expr ~ty_expect:A.Expr.bool ~notation () in
    (* TODO: read "new (x y:int)" *)
    (* TODO: read "assume expr" *)
    let+ loc2 = P.loc in
    let loc = loc1 ++ loc2 in
    A.Goal.make ~loc ~hyps:[] e
end

module P_proof : sig
  val block : notation:Notation.t -> unit -> A.Proof.block Parser.t
  val proof : notation:Notation.t -> unit -> A.Proof.t Parser.t
end = struct

  let rec proof ~notation () : A.Proof.t P.t =
    P.switch_next @@ fun tok t_loc ->
    match tok with
    | SYM "exact" ->
      `consume,
      let* e = P_meta_expr.meta_expr ~notation () in
      let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after exact proof step") in
      let loc = t_loc ++ loc2 in
      A.Proof.exact ~loc e

    | SYM "by" ->
      `consume,
      let* e = P_meta_expr.meta_expr ~notation () in
      let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after exact proof step") in
      let loc = t_loc ++ loc2 in
      A.Proof.exact ~loc e

    | SYM "subproof" ->
      `consume,
      let* goal = P_goal.goal ~notation () in
      let+ bl, loc2 = in_braces "subproof" (block ~notation ()) in
      let loc = t_loc ++ loc2 in
      A.Proof.structured ~loc goal bl

    | _ ->
      `keep,
      let+ loc2 = try_recover_semi_or_rbrace in
      let loc = t_loc ++ loc2 in
      let e =
        Error.makef ~loc "expected a proof,@ got %a" Token.pp tok
      in
      A.Proof.error ~loc e

  and block ~notation () : A.Proof.block P.t =
    block_rec ~notation []

  and block_rec ~notation acc : A.Proof.block P.t =
    P.switch_next @@ fun tok t_loc ->
    match tok with
    | SYM "have" ->
      `consume,
      let* name = P_expr.p_const in
      let* () = P.exact' EQDEF ~msg:(m_"expect `:=` after `have <name>`") in
      let* goal = P_goal.goal ~notation () in
      let* proof, loc2 = in_braces ~what:"`have` step" @@ block ~notation () in
      let loc = t_loc ++ loc2 in
      (* recurse *)
      block_rec ~notation (A.Proof.bl_have ~loc name goal proof :: acc)

    | LET ->
      `consume,
      let* var, var_loc = P_expr.p_ident in
      let var = A.Var.make ~kind:A.Var.V_normal ~loc:var_loc var None in
      let* () = P.exact' EQDEF ~msg:(m_"expect `:=` after `let <name>`") in
      let* e = P_meta_expr.meta_expr ~notation () in
      let* loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after `let <name> := <expr>") in
      let loc = t_loc ++ loc2 in
      block_rec ~notation (A.Proof.bl_let ~loc var e :: acc)

    | SYM "pick" ->
      `consume,
      let* x, x_lock = P_expr.p_ident in
      let x = A.Var.make ~kind:A.Var.V_normal ~loc:x_lock x None in
      let* () = P.exact' (SYM "where") ~msg:(m_"expect `where` after `pick <var>`") in
      let* cond = P_expr.expr ~notation () in
      let* proof, loc2 = in_braces ~what:"pick step" @@ block ~notation () in
      let loc = t_loc ++ loc2 in
      block_rec ~notation
        (A.Proof.bl_pick ~loc x cond proof :: acc)

    (* TODO: suffices *)

    | _ ->
      (* parse an atomic proof as the last step *)
      `keep,
      let* r = P.try_ (proof ~notation ()) in
      begin match r with
        | Ok pr ->
          P.return {A.Proof.steps=List.rev acc; qed=pr}

        | Error err ->
          let* _ = try_recover_semi in
          let* loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after a proof") in
          let loc = t_loc ++ loc2 in
          let pr = A.Proof.error ~loc err in
          P.return {A.Proof.steps=List.rev acc; qed=pr}
      end
end

module P_top : sig
  type top_parser =
    loc0:Loc.t -> notation:Notation.t -> unit -> A.Top.t P.t

  val parsers : (string * top_parser) list

  val top : notation:Notation.t -> unit -> A.Top.t option P.t
end = struct
  type top_parser =
    loc0:Loc.t -> notation:Notation.t -> unit -> A.Top.t P.t

  (* parse logic definition *)
  let p_def ~loc0 ~notation () : A.Top.t P.t =
    let* name = P_expr.p_const in
    let* tok, t_loc, vars =
      P_expr.p_tyvars_until ~notation []
        ~f:(function COLON | EQDEF | LBRACE -> true |_ -> false)
    in
    Log.debugf 5 (fun k->k"got vars %a, tok %a"
                     (Fmt.Dump.list A.Expr.pp_var_ty) vars Token.pp tok);
    let* tok, t_loc, ret = match tok with
      | COLON ->
        (* parse type *)
        let* e =  P_expr.expr ~ty_expect:A.Expr.type_ ~notation () in
        let+ tok, t_loc = P.next in
        tok, t_loc, Some e
      | _ ->
        P.return (tok, t_loc, None)
    in
    if not (Token.equal tok EQDEF) then (
      P.fail @@
      Error.makef ~loc:t_loc
        "expected `:=` in a definition after <vars> and optional return type,@ \
         got %a instead" Token.pp tok
    ) else (
      Log.debugf 5 (fun k->k"def: return type %a, %d vars"
                       (Fmt.Dump.option A.Expr.pp_quoted) ret (List.length vars));
      let* body = P_expr.expr ~notation () in
      let* loc2 = P.exact SEMI_COLON ~msg:(m_"expect `end` after a definition") in
      let loc = loc0 ++ loc2 in
      P.return @@ A.Top.def ~loc name vars ret body
    )

  let p_declare ~loc0 ~notation () : A.Top.t P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' COLON ~msg:(m_"expect `:` in a type declaration") in
    let* ty = P_expr.expr_atomic ~ty_expect:A.Expr.type_ ~notation () in
    Log.debugf 5 (fun k->k"parsed decl: type %a" A.Expr.pp ty);
    let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `end` after a declaration") in
    let loc = loc0 ++ loc2 in
    A.Top.decl ~loc name ty

  let p_show ~loc0 ~notation () : _ P.t =
    let* e = P_expr.expr ~notation () in
    let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after `show <expr>`") in
    let loc = loc0 ++ loc2 in
    A.Top.show ~loc e

  let p_eval ~loc0 ~notation () : _ P.t =
    let* e = P_meta_expr.meta_expr ~notation () in
    let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `;` after eval <expr>`") in
    let loc = loc0 ++ loc2 in
    A.Top.eval ~loc e

  let p_thm ~loc0 ~notation () : _ P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' EQDEF ~msg:(m_"expect `:=` after the theorem's name") in
    let* goal = P_goal.goal ~notation () in
    let+ pr, loc2 =
      in_braces ~what:"theorem statement" @@ P_proof.block ~notation () in
    let loc = loc0 ++ loc2 in
    A.Top.theorem ~loc name goal pr

  let p_goal ~loc0 ~notation () : _ P.t =
    let* goal = P_goal.goal ~notation () in
    let+ pr, loc2 =
      in_braces ~what:"goal statement" @@ P_proof.block ~notation () in
    let loc = loc0 ++ loc2 in
    A.Top.goal ~loc goal pr

  let p_fixity ~loc0 ~notation () : _ P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' EQDEF ~msg:(m_"expect `:=` after symbol") in
    let* s, s_loc = P_expr.p_ident in
    let* mkfix, needsint =
      match s with
      | "infix" -> P.return (Fixity.infix, true)
      | "prefix" -> P.return (Fixity.prefix, true)
      | "postfix" -> P.return (Fixity.postfix, true)
      | "lassoc" -> P.return (Fixity.lassoc, true)
      | "rassoc" -> P.return (Fixity.rassoc, true)
      | "binder" -> P.return (Fixity.binder, true)
      | "normal" -> P.return ((fun _->Fixity.normal), false)
      | _ ->
        P.fail @@
        Error.makef ~loc:s_loc
          "expected one of: normal|infix|prefix|postfix|lassoc|rassoc|binder@ \
           but got '%s'" s
    in
    let* n =
      if needsint then (
        P.switch_next @@ fun n _loc ->
        match n with
        | NUM n -> `consume, P.return (int_of_string n)
        | _ -> `keep, P.fail_str "expect a number after `fixity`"
      ) else P.return 0
    in
    let fix = mkfix n in
    let+ loc2 = P.exact SEMI_COLON ~msg:(m_"expect `end` after fixity declarations") in
    let loc = loc0 ++ loc2 in
    A.Top.fixity ~loc name fix

  (* TODO: make it extensible *)
  (* list of toplevel parsers *)
  let parsers : (string * top_parser) list = [
    "def", p_def;
    "show", p_show;
    "eval", p_eval;
    "fixity", p_fixity;
    "declare", p_declare;
    "theorem", p_thm;
    "goal", p_goal;
  ]

  let top ~notation () : A.Top.t option P.t =
    Log.debugf 1 (fun k->k"parse top");
    let errm ~loc tok =
      Error.makef ~loc
        "expected toplevel statement, but got token %a;@ expected one of: [%s]"
        Token.pp tok
        (String.concat "," @@ List.map (fun (s,_) -> String.escaped s) parsers)
    in
    let* loc0 = P.loc in
    let* res =
      P.try_ @@
      P.switch_next @@ fun tok0 loc0 ->
      match tok0 with
      | EOF ->
        `keep, P.return None
      | SYM s ->
        `consume,
        begin match List.assoc s parsers with
          | exception Not_found ->
            Log.debugf 5 (fun k->k"unknown toplevek tok %a" Token.pp tok0);
            let err = errm ~loc:loc0 tok0 in
            let* _ = try_recover_semi in
            let+ loc2 = P.exact SEMI_COLON
                ~msg:(m_"expect semicolon after an unknown statement.") in
            let loc = loc0 ++ loc2 in
            Some (A.Top.error ~loc err)
          | p ->
            Log.debugf 5 (fun k->k"parse toplevel %s" s);
            let+ x = p ~loc0 ~notation () in
            Some x
        end
      | _ ->
        `keep,
        let err = errm ~loc:loc0 tok0 in
        let* _ = try_recover_semi in
        let+ loc2 = P.exact SEMI_COLON
            ~msg:(m_"expect semicolon after a toplevel statement") in
        let loc = loc0 ++ loc2 in
        Some (A.Top.error ~loc err)
    in
    begin match res with
      | Ok r -> P.return r
      | Error err ->
        Log.debugf 0 (fun k->k"error %a" Error.pp err);
        let* _ = try_recover_semi in
        let+ loc2 = P.exact SEMI_COLON
            ~msg:(m_"expect semicolon after toplevel statement") in
        let loc = loc0 ++ loc2 in
        let err = Error.wrap ~loc "parsing a toplevel statement" err in
        Some (A.Top.error ~loc err)
    end
end

let parse_expr ~notation () : A.Expr.t P.t =
  P.parsing (Error.wrap "parsing expression") @@
  P_expr.expr_and_eof ~notation ()

let parse_top = P_top.top

let parse_top_l ~notation () : A.Top.t list P.t =
  let rec loop acc =
    let* r = P_top.top ~notation:(!notation) () in
    match r with
    | None -> P.return (List.rev acc)
    | Some st ->
      begin match st.A.view with
        | A.Top.Fixity {name; fixity} ->
          Notation.Ref.declare notation (A.Const.name name) fixity
        | _ -> ()
      end;
      loop (st::acc)
  in
  loop []
