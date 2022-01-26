
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


(* recover: skip to the next ";", without consuming it *)
let try_recover_semi : Loc.t P.t =
  let rec loop loc0 =
    P.switch_next @@ fun tok loc ->
    match tok with
    | SEMI_COLON | EOF ->
      `keep, P.return (loc0++loc)
    | _ ->
      `consume, loop loc0
  in

  let* loc = P.loc in
  loop loc

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
      let+ () = P.rparen ~msg:"expected a closing ')' after an atomic expression" () in
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
      let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after exact proof step" in
      let loc = t_loc ++ loc2 in
      A.Proof.exact ~loc e

    | SYM "by" ->
      `consume,
      let* e = P_meta_expr.meta_expr ~notation () in
      let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after exact proof step" in
      let loc = t_loc ++ loc2 in
      A.Proof.exact ~loc e

    | SYM "subproof" ->
      `consume,
      let* goal = P_goal.goal ~notation () in
      let* () = P.exact' LBRACE ~msg:"expect `{` to open the subproof" in
      let* bl = block ~notation () in
      let* () = P.exact' RBRACE ~msg:"expect closing `}` after the subproof" in
      let* loc2 = P.exact SEMI_COLON ~msg:"expect `;` after the subproof" in
      let loc = t_loc ++ loc2 in
      P.return @@ A.Proof.structured ~loc goal bl

    | _ ->
      `keep,
      let* _ = try_recover_semi in
      let+ loc2 = P.exact SEMI_COLON ~msg:"expect semicolon after a proof" in
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
      let* () = P.exact' EQDEF ~msg:"expect `:=` after `have <name>`" in
      let* goal = P_goal.goal ~notation () in
      let* () = P.exact' LBRACE ~msg:"expect `{` after `have <name> := <goal>`" in
      let* proof = block ~notation () in
      let* () = P.exact' RBRACE ~msg:"expect closing `}`" in
      let* loc2 = P.exact SEMI_COLON ~msg:"expect `;` after `have` step" in
      let loc = t_loc ++ loc2 in
      (* recurse *)
      block_rec ~notation (A.Proof.bl_have ~loc name goal proof :: acc)

    | SYM "let" ->
      `consume,
      let* var, var_loc = P_expr.p_ident in
      let var = A.Var.make ~kind:A.Var.V_normal ~loc:var_loc var None in
      let* () = P.exact' EQDEF ~msg:"expect `:=` after `let <name>`" in
      let* e = P_meta_expr.meta_expr ~notation () in
      let* loc2 = P.exact SEMI_COLON ~msg:"expect `;` after `let <name> := <expr>" in
      let loc = t_loc ++ loc2 in
      block_rec ~notation (A.Proof.bl_let ~loc var e :: acc)

    | SYM "pick" ->
      `consume,
      let* x, x_lock = P_expr.p_ident in
      let x = A.Var.make ~kind:A.Var.V_normal ~loc:x_lock x None in
      let* () = P.exact' (SYM "where") ~msg:"expect `where` after `pick <var>`" in
      let* cond = P_expr.expr ~notation () in
      let* () = P.exact' LBRACE ~msg:"expect `{` after `pick <name> where <cond>`" in
      let* proof = block ~notation () in
      let* () = P.exact' RBRACE ~msg:"expect closing `}`" in
      let* loc2 = P.exact SEMI_COLON ~msg:"expect `;` after pick` step" in
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
          let* loc2 = P.exact SEMI_COLON ~msg:"expect `;` after a proof" in
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
      let* loc2 = P.exact SEMI_COLON ~msg:"expect `end` after a definition" in
      let loc = loc0 ++ loc2 in
      P.return @@ A.Top.def ~loc name vars ret body
    )

  let p_declare ~loc0 ~notation () : A.Top.t P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' COLON ~msg:"expect `:` in a type declaration" in
    let* ty = P_expr.expr_atomic ~ty_expect:A.Expr.type_ ~notation () in
    Log.debugf 5 (fun k->k"parsed decl: type %a" A.Expr.pp ty);
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `end` after a declaration" in
    let loc = loc0 ++ loc2 in
    A.Top.decl ~loc name ty

  let p_show ~loc0 ~notation () : _ P.t =
    let* e = P_expr.expr ~notation () in
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after `show <expr>`" in
    let loc = loc0 ++ loc2 in
    A.Top.show ~loc e

  let p_eval ~loc0 ~notation () : _ P.t =
    let* e = P_meta_expr.meta_expr ~notation () in
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after eval <expr>`" in
    let loc = loc0 ++ loc2 in
    A.Top.eval ~loc e

  let p_thm ~loc0 ~notation () : _ P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' EQDEF ~msg:"expect `:=` after the theorem's name" in
    let* goal = P_goal.goal ~notation () in
    let* () = P.exact' LBRACE ~msg:"expect `{` after the theorem's statement" in
    let* pr = P_proof.block ~notation () in
    let* () = P.exact' RBRACE ~msg:"expect `}` after the theorem" in
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after the theorem" in
    let loc = loc0 ++ loc2 in
    A.Top.theorem ~loc name goal pr

  let p_goal ~loc0 ~notation () : _ P.t =
    let* goal = P_goal.goal ~notation () in
    let* () = P.exact' LBRACE ~msg:"expect `{` after the goal's statement" in
    let* pr = P_proof.block ~notation () in
    let* () = P.exact' RBRACE ~msg:"expect `}` after the goal" in
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `;` after the goal" in
    let loc = loc0 ++ loc2 in
    A.Top.goal ~loc goal pr

  let p_fixity ~loc0 ~notation () : _ P.t =
    let* name = P_expr.p_const in
    let* () = P.exact' EQDEF ~msg:"expect `:=` after symbol" in
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
    let+ loc2 = P.exact SEMI_COLON ~msg:"expect `end` after fixity declarations" in
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
                ~msg:"expect semicolon after an unknown statement." in
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
            ~msg:"expect semicolon after a toplevel statement" in
        let loc = loc0 ++ loc2 in
        Some (A.Top.error ~loc err)
    in
    begin match res with
      | Ok r -> P.return r
      | Error err ->
        Log.debugf 0 (fun k->k"error %a" Error.pp err);
        let* _ = try_recover_semi in
        let+ loc2 = P.exact SEMI_COLON
            ~msg:"expect semicolon after toplevel statement" in
        let loc = loc0 ++ loc2 in
        let err = Error.wrap ~loc "expected a toplevel statement" err in
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
