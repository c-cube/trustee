
(** {1 Expression parser} *)

open Common_

module A = Parse_ast
module LL = Local_loc
module P = Parser

open Loc.Infix
open P.Infix

(*
module P_state = struct
  type t = {
    notation: Notation.Ref.t;
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

  let eat_semi ~msg self : Loc.t =
    let _, loc = eat_p self ~msg ~f:(function SEMI_COLON -> true | _ -> false) in
    loc

  let eat_semi' ~msg self : unit =
    ignore (eat_semi self ~msg : Loc.t)

  (* recover: skip to the next ";" *)
  let try_recover_semi (self:t) : Loc.t =
    let loc = ref (snd @@ Lexer.S.cur self.lex) in
    Log.debugf 1 (fun k->k"try recover semi at %a" Loc.pp !loc);
    while
      let tok, tok_loc = Lexer.S.cur self.lex in
      match tok with
      | SEMI_COLON | EOF ->
        loc := Loc.(tok_loc ++ !loc);
        false
      | _ -> Lexer.S.consume self.lex; true
    do () done;
    !loc
end
   *)

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
      let* () = P.exact' EQDEF ~msg:"`:=` in let binding" in
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
        let* () = P.exact' RPAREN ~msg:"expect ')' after a group of typed variables" in
        p_tyvars_until ~notation ~f (List.rev_append l acc)
      | SYM _ ->
        `keep,
        let* l = p_tyvar_grp_ ~notation () in
        let+ last, _ = P.token_if f ~msg:"`.` terminating list of bound variables" in
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
      let+ () = P.rparen ~msg:"atomic expression" () in
      e
    | LET ->
      `consume,
      (* parse `let x = e in e2` *)
      let* bs = p_bindings_ ~notation ~bindings () in
      let* () = P.exact' IN ~msg:"let binding body" in
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
          let* vars = p_tyvars_and_dot ~notation [] in
          let+ body = p_expr_ ~bindings ~notation ~ty_expect i in
          let loc = loc_t ++ A.Expr.loc body in
          begin match s with
            | "\\" -> A.Expr.lambda ~loc vars body
            | "with" -> A.Expr.with_ ~loc vars body
            | _ ->
              let b = A.Const.make ~loc:loc_t (Name.make s) in
              A.Expr.bind ~loc b vars body
          end
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
    | BY | LBRACE | RBRACE | EQDEF | SEMI_COLON
    | COMMA | SINGLE_QUOTE ->
      `keep, P.fail_str "expected expression"

  and p_expr_app_ ~bindings ~notation ~ty_expect () : A.Expr.t P.t =
    let rec loop e : A.Expr.t P.t =
      P.switch_next @@ fun tok loc_t ->
      match tok with
      | LPAREN ->
        `consume,
        let* e2 = p_expr_ ~notation ~bindings ~ty_expect:None 0 in
        let* () = P.rparen ~msg:"expect `)` to close sub-expression" () in
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
      | (EOF | LBRACE | RBRACE | BY | EQDEF) ->
        `keep, P.return lhs

      | LPAREN ->
        `consume,
        let* e = p_expr_ ~bindings ~notation ~ty_expect:None 0 in
        let* () = P.rparen ~msg:"closing `)` in expression" () in
        loop (A.Expr.app lhs [e]) p

      | (RPAREN | WILDCARD | COLON | DOT | IN | COMMA | SEMI_COLON
        | LET | AND | SINGLE_QUOTE) ->
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
    let* () = P.eoi ~msg:"expected end of input after expression" () in
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
      | LBRACE | RBRACE ->
        `consume,
        P.return @@ A.Subst.mk_ ~loc:(loc1 ++ loc_t) (List.rev s)

      | COMMA when expect_comma ->
        `consume,
        p_binding ~expect_comma:false s

      | _ ->
        `keep,
        if expect_comma then (
          P.fail_str "expected `,` or `end` after a substitution binding"
        ) else (
          let* v, loc_v = P_expr.p_ident in
          let* () = P.exact' EQDEF ~msg:"expect `:=` in substitution" in
          let* e = P_expr.expr ~notation () in
          let s = ({A.view=v;loc=loc_v},e)::s in
          p_binding ~expect_comma:true s
        )
    in
    let* () = P.exact' (SYM "subst") ~msg:"expect `subst`" in
    p_binding ~expect_comma:false []
end

module P_meta_expr : sig
  val meta_expr :
    notation:Notation.t ->
    unit ->
    A.Meta_expr.t P.t
end = struct
  let meta_expr ~notation () : A.Meta_expr.t P.t =
    P.fail_str "TODO"
    (* TODO
    let tok, t_loc = Lexer.S.cur self.lex in
    Lexer.S.consume self.lex;
    A.Meta_expr.mk ~loc:t_loc
      (A.Meta_expr.Error (Error.make ~loc:t_loc "TODO: meta_expr"))
       *)
end

module P_proof : sig
  val block : A.Proof.block parser_
  val proof : A.Proof.t parser_
end = struct
  open P_state
  open Loc.Infix

  (* parse a sequent *)
  let goal (self:t) : A.Proof.sequent =
    let _, loc1 = Lexer.S.cur self.lex in
    let e = P_expr.expr self in
    let _, loc2 = Lexer.S.cur self.lex in
    (* TODO: read "new (x y:int)" *)
    (* TODO: read "assume expr" *)
    let loc = loc1 ++ loc2 in
    A.Proof.mk_sequent ~loc ~hyps:[] ~goal:e ()

  let rec proof (self:t) : A.Proof.t =
    Log.debugf 5 (fun k->k"start parsing proof");
    match Lexer.S.cur self.lex with
    | SYM "exact", t_loc ->
      Lexer.S.consume self.lex;
      let e = P_meta_expr.meta_expr self in
      let loc =
        t_loc ++ eat_semi self ~msg:"expect `;` after exact proof step" in
      A.Proof.exact ~loc e

    | SYM "by", t_loc ->
      Lexer.S.consume self.lex;
      let e = P_meta_expr.meta_expr self in
      let loc =
        t_loc ++ eat_semi self ~msg:"expect `;` after exact proof step" in
      A.Proof.exact ~loc e

    | tok, loc ->
      let loc = loc ++ try_recover_semi self in
      eat_semi' self ~msg:"expect semicolon after a proof";
      let e =
        Error.makef ~loc "expected a proof,@ got %a" Token.pp tok
      in
      A.Proof.error ~loc e

  and block (self:t) : A.Proof.block =
    block_rec self []

  and block_rec self acc : A.Proof.block =
    match Lexer.S.cur self.lex with
    | SYM "have", t_loc ->
      Lexer.S.consume self.lex;
      let name = P_expr.p_const self in
      eat_eq' self EQDEF ~msg:"expect `:=` after `have <name>`";
      let goal = goal self in
      eat_eq' self LBRACE ~msg:"expect `{` after `have <name> := <goal>`";
      let proof = block self in
      eat_eq' self RBRACE ~msg:"expect closing `}`";
      let loc = t_loc ++ eat_semi self ~msg:"expect `;` after `have` step" in
      block_rec self (A.Proof.bl_have ~loc name goal proof :: acc)

    | SYM "let", t_loc ->
      Lexer.S.consume self.lex;
      let var, var_loc = P_expr.p_ident self in
      let var = A.Var.make ~kind:A.Var.V_normal ~loc:var_loc var None in
      eat_eq' self EQDEF ~msg:"expect `:=` after `have <name>`";
      let e = P_meta_expr.meta_expr self in
      let loc = t_loc ++ eat_semi self ~msg:"expect `;` after `have` step" in
      block_rec self (A.Proof.bl_let ~loc var e :: acc)

    | SYM "pick", t_loc ->
      Lexer.S.consume self.lex;
      let x, x_lock = P_expr.p_ident self in
      let x = A.Var.make ~kind:A.Var.V_normal ~loc:x_lock x None in
      eat_eq' self (SYM "where") ~msg:"expect `where` after `pick <var>`";
      let cond = P_expr.expr self in
      eat_eq' self LBRACE ~msg:"expect `{` after `pick <name> where <cond>`";
      let proof = block self in
      eat_eq' self RBRACE ~msg:"expect closing `}`";
      let loc = t_loc ++ eat_semi self ~msg:"expect `;` after pick` step" in
      block_rec self
        (A.Proof.bl_pick ~loc x cond proof :: acc)

    (* TODO: suffices *)

    | _, t_loc ->
      (* parse an atomic proof as the last step *)
      try
        let pr = proof self in
        {A.Proof.steps=List.rev acc; qed=pr}
      with Error.E err ->
        let loc = t_loc ++ try_recover_semi self in
        eat_semi' self ~msg:"expect semicolon after a proof item.";
        let pr = A.Proof.error ~loc err in
        {A.Proof.steps=List.rev acc; qed=pr}
end

module P_top = struct
  open P_state
  open Loc.Infix

  (* parse logic definition *)
  let p_def ~loc:loc0 self : A.Top.t =
    let name, loc_name = P_expr.p_ident self in
    let tok, t_loc, vars =
      P_expr.p_tyvars_until self []
        ~f:(function COLON | EQDEF | LBRACE -> true |_ -> false)
    in
    Log.debugf 5 (fun k->k"got vars %a, tok %a"
                     (Fmt.Dump.list A.Expr.pp_var_ty) vars Token.pp tok);
    let tok, t_loc, ret = match tok with
      | COLON ->
        (* parse type *)
        let e =  P_expr.expr ~ty_expect:A.Expr.type_ self in
        let tok, t_loc = Lexer.S.cur self.lex in
        Lexer.S.consume self.lex;
        tok, t_loc, Some (e)
      | _ -> tok, t_loc, None
    in
    if not (Token.equal tok EQDEF) then (
      Error.failf ~loc:t_loc
        (fun k->k"expected `:=` in a definition after <vars> and optional return type,@ \
                  got %a instead" Token.pp tok)
    );
    Log.debugf 5 (fun k->k"def: return type %a, %d vars, current token: %a"
                     (Fmt.Dump.option A.Expr.pp_quoted) ret (List.length vars)
                     Token.pp (fst @@ Lexer.S.cur self.lex));
    let body = P_expr.expr self in
    let loc = loc0 ++ eat_semi self ~msg:"expect `end` after a definition" in
    A.Top.def ~loc (A.Const.make_str ~loc:loc_name name) vars ret body

  let p_declare ~loc self : A.Top.t =
    let name, loc_name = P_expr.p_ident self in
    eat_eq' self COLON ~msg:"expect `:` in a type declaration";
    let ty = P_expr.expr_atomic ~ty_expect:A.Expr.type_ self in
    Log.debugf 5 (fun k->k"parsed decl: type %a" A.Expr.pp ty);
    let loc = loc ++ eat_semi self ~msg:"expect `end` after a declaration" in
    A.Top.decl ~loc {A.view=name;loc=loc_name} ty

  let p_show ~loc self : _ =
    let e = P_expr.expr self in
    let loc = loc ++ eat_semi self ~msg:"expect `;` after `show <expr>`" in
    A.Top.show ~loc e

  let p_eval ~loc self : _ =
    let e = P_meta_expr.meta_expr self in
    let loc = loc ++ eat_semi self ~msg:"expect `;` after eval <expr>`" in
    A.Top.eval ~loc e

  let p_thm ~loc self : _ =
    let name, loc_name = P_expr.p_ident self in
    eat_eq' self EQDEF ~msg:"expect `:=` after the theorem's name";
    let e = P_expr.expr self ~ty_expect:A.Expr.bool in
    eat_eq' self LBRACE ~msg:"expect `{` after the theorem's statement";
    let pr = P_proof.block self in
    eat_eq' self RBRACE ~msg:"expect `}` after the theorem";
    let loc = loc ++ eat_semi self ~msg:"expect `;` after the theorem" in
    A.Top.theorem ~loc (A.Const.make_str ~loc:loc_name name)
      (A.Goal.make_nohyps ~loc e) pr

  let p_goal ~loc self : _ =
    let e = P_expr.expr self ~ty_expect:A.Expr.bool in
    eat_eq' self LBRACE ~msg:"expect `{` after the goal's statement";
    let pr = P_proof.block self in
    eat_eq' self RBRACE ~msg:"expect `}` after the goal";
    let loc = loc ++ eat_semi self ~msg:"expect `;` after the goal" in
    A.Top.goal ~loc (A.Goal.make_nohyps ~loc e) pr

  let p_fixity ~loc self =
    let name, loc_name = P_expr.p_ident self in
    eat_eq' self EQDEF ~msg:"expect `:=` after symbol";
    let mkfix, needsint =
      match fst @@ P_expr.p_ident self with
      | "infix" -> Fixity.infix, true
      | "prefix" -> Fixity.prefix, true
      | "postfix" -> Fixity.postfix, true
      | "lassoc" -> Fixity.lassoc, true
      | "rassoc" -> Fixity.rassoc, true
      | "binder" -> Fixity.binder, true
      | "normal" -> (fun _->Fixity.normal), false
      | s ->
        Error.failf ~loc:loc_name
          (fun k->k
              "expected one of: normal|infix|prefix|postfix|lassoc|rassoc|binder@ \
               but got '%s'" s)
    in
    let n =
      if needsint then (
        let n, _ = eat_p self ~msg:"expect a number after fixity"
            ~f:(function NUM _ -> true | _ -> false)
        in
        match n with NUM s -> int_of_string s | _ -> assert false
      ) else 0
    in
    let fix = mkfix n in
    let loc = loc ++ eat_semi self ~msg:"expect `end` after fixity declarations" in
    A.Top.fixity ~loc {A.view=name;loc=loc_name} fix

  (* TODO: make it extensible *)
  (* list of toplevel parsers *)
  let parsers = [
    "def", p_def;
    "show", p_show;
    "eval", p_eval;
    "fixity", p_fixity;
    "declare", p_declare;
    "theorem", p_thm;
    "goal", p_goal;
  ]

  let top (self:t) : A.Top.t option =
    Log.debugf 1 (fun k->k"parse top");
    let parsing = ref None in
    let errm ~loc tok =
      Error.makef ~loc
        "expected toplevel statement, but got token %a;@ expected one of: [%s]"
        Token.pp tok
        (String.concat "," @@ List.map (fun (s,_) -> String.escaped s) parsers)
    in
    try
      match Lexer.S.cur self.lex with
      | EOF, _ -> None
      | SYM s as t, loc ->
        begin match List.assoc s parsers with
          | exception Not_found ->
            Log.debugf 5 (fun k->k"unknown toplevek tok %a" Token.pp t);
            let err = errm ~loc t in
            let loc = loc ++ try_recover_semi self in
            eat_semi' self
              ~msg:"expect semicolon after an unknown statement.";
            Some (A.Top.error ~loc err)
          | p ->
            parsing := Some s;
            Log.debugf 5 (fun k->k"parse toplevel %s" s);
            Lexer.S.consume self.lex;
            Some (p ~loc self)
        end
      | tok, loc ->
        let err = errm ~loc tok in
        let loc = loc ++ try_recover_semi self in
        eat_semi' self ~msg:"expect semicolon after a toplevel statement";
        Some (A.Top.error ~loc err)
    with
    | Error.E err ->
      Log.debugf 0 (fun k->k"error %a" Error.pp err);
      let _, loc = Lexer.S.cur self.lex in
      let loc = loc ++ try_recover_semi self in
      eat_semi' self ~msg:"expect semicolon after toplevel statement";
      let err =
        let parsing out () = match !parsing with
          | None -> ()
          | Some p -> Fmt.fprintf out "@ while parsing `%s`" p
        in
        Error.wrapf ~loc
          "expected a toplevel statement%a" parsing () err
      in
      Some (A.Top.error ~loc err)
end

let parse_expr ~notation lex : A.Expr.t =
  let p = P_state.create ~notation lex in
  let e =
    Error.guard (Error.wrap "parsing expression") @@ fun () ->
    P_expr.expr_and_eof p
  in
  e

let parse_top ~notation lex : A.Top.t option =
  let p = P_state.create ~notation lex in
  let st = P_top.top p in
  Log.debugf 1 (fun k->k"parsed %a" (Fmt.Dump.option A.Top.pp_quoted) st);
  st

let parse_top_l ~notation lex : A.Top.t list =
  let rec aux acc =
    match parse_top ~notation lex with
    | None -> List.rev acc
    | Some st ->
      begin match st.A.view with
        | A.Top.Fixity {name; fixity} ->
          Notation.Ref.declare notation (Name.make name.A.view) fixity
        | _ -> ()
      end;
      aux (st::acc)
  in
  aux []
