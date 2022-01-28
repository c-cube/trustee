

open Common_

module A = Parse_ast
module SD = Sexp_decode
module Sexp = Sexp_loc

open SD.Infix

let spf = Printf.sprintf

type t = {
  notation: Notation.Ref.t;
}
type 'a parser = t -> 'a SD.t
type 'a or_error = ('a, Loc.t * Error.t) result

module Or_error = struct
  type 'a t = 'a or_error
  let get_exn = function
    | Ok x -> x
    | Error (_, err) -> Error.raise err

  exception E of Loc.t * Error.t

  let sequence_l l =
    try Ok (CCList.map (function Ok x -> x | Error (loc, err) -> raise (E(loc,err))) l)
    with E (loc,err) -> Error (loc,err)
end

let run (self:t) ~filename str (p:'a parser) : _ list =
  let se_p = Sexp.Parse.create ~filename str in
  let rec loop acc = match Sexp.Parse.parse1 se_p with
    | None -> List.rev acc
    | Some sexp ->
      Log.debugf 5 (fun k->k"parse S-expr %a" Sexp.pp sexp);
      begin match SD.run (p self) sexp with
        | Ok r -> loop (Ok r::acc)
        | Error sd_err ->
          let loc = SD.Err.loc sd_err in
          let err = SD.Err.to_error sd_err in
          loop (Error (loc, err) :: acc)
      end
  in
  loop []

let run_exn (self:t) ~filename str p : _ list =
  let se_p = Sexp.Parse.create ~filename str in
  let rec loop acc = match Sexp.Parse.parse1 se_p with
    | None -> List.rev acc
    | Some sexp ->
      Log.debugf 5 (fun k->k"parse S-expr %a" Sexp.pp sexp);
      begin match SD.run (p self) sexp with
        | Ok r -> loop (r::acc)
        | Error sd_err ->
          let err = SD.Err.to_error sd_err in
          Error.raise err
      end
  in
  loop []

let create ~notation () : t =
  { notation; }

let p_var ~p_ty () =
  let* v = SD.value in
  let loc = v.Sexp.loc in
  match v.Sexp.view with
  | Sexp.Atom name -> SD.return @@ A.Var.make ~loc name None
  | Sexp.List [{Sexp.view=Sexp.Atom name; _}; ty] ->
    (* [x ty] is [x : ty] *)
    let+ ty = SD.sub p_ty ty in
    A.Var.make ~loc name (Some ty)
  (* TODO: parse as `$ (x : ty) $`
  | Sexp.Dollar _ ->
  *)
  | _ ->
    SD.fail "expected a variable"

module P_expr : sig
  val top : A.Expr.t parser
end = struct
  let doc =
{|expected a logical expression.

Such expressions can be built as follows:

- $ <expr> $ using predefined notations and user-defined notations.
  For example, $ \(x y:bool). x=y $ is a lambda-term.
- (expr/app <expr> <expr>+) is a function application.
- (expr/var <var>) is a variable node. A variable is either a name "x"
    or a pair (x <type>).
- (expr/lam (<var>*) <expr>) is a lambda abstraction.
- (expr/const "name" <expr>*) is a constant, with its type arguments.
- expr/type is Type, the type of types.
- (expr/arrow <expr>+ <expr>) is the function arrow type. (expr/arrow a b c)
  builds the type `a -> b -> c`.

|}

  (* either parse a $ foo $ value, or a s-expr *)
  let top (self:t) : _ SD.t =
    SD.fix @@ fun expr ->
    SD.try_l ~msg:"expected a logical expression" [

      (SD.is_atom_of "expr/type", SD.return A.Expr.type_);

      (SD.is_applied "expr/app",
       let* l = SD.applied "expr/app" SD.value in
       begin match l with
         | [] | [_] -> SD.fail "expr/app needs at least 2 arguments"
         | f :: args ->
           let+ f = SD.sub expr f
           and+ args = SD.map_l (SD.sub expr) args in
           A.Expr.app f args
       end);

      (SD.is_applied "expr/arrow",
       let* loc = SD.loc in
       let* l = SD.applied "expr/arrow" SD.value in
       begin match l with
         | [] | [_] -> SD.fail "expr/arrow needs at least 2 arguments"
         | l ->
           let+ l = SD.map_l (SD.sub expr) l in
           match List.rev l with
           | ret :: args -> A.Expr.ty_arrow ~loc (List.rev args) ret
           | [] -> assert false
       end);

      (SD.is_applied "expr/lam",
       let* loc = SD.loc in
       let+ vars, bod =
         SD.applied2 "expr/lam"
           SD.(list_of ~what:"typed variables" @@ p_var ~p_ty:expr ()) expr in
       A.Expr.lambda ~loc vars bod);

      (SD.is_applied "expr/var",
       let* loc = SD.loc in
       let+ v = SD.applied1 "expr/var" (p_var ~p_ty:expr ()) in
       A.Expr.var ~loc v);

      (SD.is_applied "expr/const",
       let* loc = SD.loc in
       let* l = SD.applied "expr/const" SD.value in
       begin match l with
         | [] -> SD.fail "expr/const needs at least one argument"
         | [c] ->
           let+ c = SD.sub SD.atom c in
           A.Expr.const ~loc (A.Const.make ~loc (Name.make c)) None

         | c :: args ->
           let+ c = SD.sub SD.atom c
           and+ c_loc = SD.sub SD.loc c
           and+ args = SD.map_l (SD.sub expr) args in
           A.Expr.const ~loc (A.Const.make ~loc:c_loc (Name.make c)) (Some args)
       end);

      (* parse expression in "$" … "$" *)
      (SD.is_dollar_str,
       (* get current loc to get the starting offset.
          this is required to get accurate locations inside the expression,
          even though it's parsed from a {i slice} of the original input. *)
       let* loc = SD.loc in
       let loc_offset = Loc.local_loc loc |> Loc.LL.offsets |> fst in
       let filename = Loc.filename loc in
       let* s = SD.dollar_str in
       begin match
           Expr_parser.expr_of_string s
             ~loc_offset ~notation:!(self.notation) ~file:filename
         with
         | Ok e ->
           SD.return e
         | Error (loc, err) ->
           let expr = A.Expr.error ~loc err in
           SD.return expr
       end);

    ]

end

module P_subst : sig
  val top : A.Subst.t parser
end = struct
  let top (self:t) : _ SD.t =
    let pexpr = P_expr.top self in
    let pvar = p_var ~p_ty:pexpr () in
    let* loc = SD.loc in
    let+ l = SD.applied "subst" (SD.pair pvar pexpr) in
    A.Subst.mk_ ~loc l
end

(* TODO
module P_meta_expr : sig
  val meta_expr : A.Meta_expr.t parser
end = struct
  module E = A.Meta_expr

  let p_var = SD.atom

  let rec meta_expr_rec_ ~notation () : _ SD.t =
    SD.switch_next @@ fun tok t_loc ->
    begin match tok with
      | NUM n ->
        (* TODO: handle int parsing error *)
        `consume,
        SD.return @@ E.mk ~loc:t_loc (E.Value (E.V_int (int_of_string n)))

      | SYM (("true" | "false") as b) ->
        `consume,
        SD.return @@ E.mk ~loc:t_loc (E.Value (E.V_bool (bool_of_string b)))

      | QUOTED_STR s ->
        `consume,
        SD.return @@ E.mk ~loc:t_loc (E.Value (E.V_string s))

      | LBRACE ->
        (* parse a block *)
        `consume,
        let* bl, loc = block_stmts ~notation [] in
        SD.return @@ E.mk ~loc (E.Block_expr bl)

      | LBRACKET ->
        `consume,
        (* TODO: comprehensions *)
        let* l =
          list_many ~what:"meta-expressions" ~sep:COMMA ~stop:RBRACKET @@
          meta_expr_rec_ ~notation () in
        let* loc2 =
          SD.exact RBRACKET ~msg:(m_"expect closing `]` after list literal") in
        let loc = t_loc ++ loc2 in
        SD.return @@ E.mk ~loc (E.List_lit l)

      | DOLLAR ->
        `consume,
        let* e = P_expr.expr ~notation () in
        let+ loc2 = SD.exact DOLLAR ~msg:(m_ "expect closing `$` after expression") in
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
        SD.switch_next @@ fun tok2 loc2 ->
        begin match tok2 with
          | SINGLE_QUOTE ->
            (* c'accessor *)
            `consume,
            let* accessor = P_expr.p_const in
            let+ loc2 = SD.loc in
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
        SD.switch_next @@ fun tok2 loc2 ->
        begin match tok2 with
          | RPAREN ->
            `consume,
            SD.return @@ E.mk ~loc:t_loc (E.Value (E.V_unit))

          | _ ->
            (* parse sub-expression *)
            `keep,
            let* e = meta_expr_rec_ ~notation () in
            let+ () = SD.exact' RPAREN ~msg:(m_"expect closing `)` after expression") in
            e

        end

      | ERROR c ->
        (* lexer error *)
        `consume,
        let err = Error.makef ~loc:t_loc "expected meta-expression, not %C" c in
        SD.return @@ E.mk ~loc:t_loc (E.Error err)

      | EQDEF | IN | AND | WILDCARD | SINGLE_QUOTE | DOT | RBRACKET
      | COMMA | SEMI_COLON | RPAREN | QUESTION_MARK | QUOTE_STR _
      | QUESTION_MARK_STR _ | RBRACE | COLON | EOF | LET | FAT_ARROW ->
        `keep,
        SD.fail_str "expected meta-expression"
    end

  and meta_expr_apply_ ~notation lhs : E.t SD.t =
    SD.switch_next @@ fun tok t_loc ->
    match tok with
    | RPAREN | RBRACKET | RBRACE | SEMI_COLON ->
      `keep,
      SD.return lhs

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

  and block_stmt ~notation () : (E.block_stmt * [`last | `any]) SD.t =
    SD.parsing (Error.wrap "parsing a block statement") @@
    SD.switch_next @@ fun tok loc ->
    match tok with
    | RBRACE ->
      `keep, SD.fail_str "expected statement"
    | LET ->
      `consume,
      let* x, x_loc = p_var in
      let x = A.Var.make ~loc:x_loc x None in
      let* () = SD.exact' EQDEF ~msg:(m_"expect `:=` in let binding") in
      let* e = meta_expr_rec_ ~notation () in
      let* loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after let binding") in

      let stmt = E.mk_bl ~loc:(loc++loc2) @@ E.Blk_let (x,e) in
      SD.return (stmt, `any)

    | SYM "return" ->
      `consume,
      let* e = meta_expr_rec_ ~notation () in
      let* loc3 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after `return <expr>`") in
      let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_return e in
      SD.return (stmt, `last)

    | IF ->
      `consume,
      let* test = meta_expr_rec_ ~notation () in
      let* (then_,_), loc1 = in_braces ~what:"if branch" @@ block_stmts ~notation [] in

      let rec p_rest elseifs loc =
        SD.switch_next @@ fun tok2 loc2 ->
        match tok2 with
        | SYM "else" ->
          `consume,
          SD.switch_next @@ fun tok3 _ ->
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
            SD.return (List.rev elseifs, Some bl, loc)
          )
        | _ ->
          `keep,
          SD.return (List.rev elseifs, None, loc)
      in

      let* else_ifs, else_, loc2 = p_rest [] loc1 in
      let loc = loc ++ loc2 in
      let stmt = E.mk_bl ~loc @@ E.Blk_if {test; then_; else_ifs; else_} in
      SD.return (stmt, `any)

    | _ ->
      (* parse either [e] or [e;] *)
      `keep,
      let* e = meta_expr_rec_ ~notation () in
      begin
        SD.switch_next @@ fun tok3 loc3 ->
        match tok3 with
        | SEMI_COLON ->
          `consume,
          let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_eval_seq e in
          SD.return (stmt, `any)

        | _ ->
          `keep,
          let stmt = E.mk_bl ~loc:(loc++loc3) @@ E.Blk_eval e in
          SD.return (stmt, `last)
      end

  (* read a block, return the `}`'s location *)
  and block_stmts ~notation acc : (E.block_expr * Loc.t) SD.t =
    SD.switch_next @@ fun tok loc ->
    match tok with
    | RBRACE ->
      `consume,
      let bl = {E.stmts=List.rev acc} in
      SD.return (bl, loc)

    | _ ->
      `keep,
      let* st, islast =
        let* r = SD.try_ @@ block_stmt ~notation () in
        match r with
        | Ok x -> SD.return x
        | Error err ->
          (* catch errors and wrap them *)

          let* () = (* make sure to make progress *)
            let* loc2 = SD.loc in
            if Loc.same_local_loc loc loc2
            then let+ _ = SD.next in () else SD.return () in (* skip *)

          let* loc = try_recover_semi_or_rbrace in
          let bl = E.mk_bl ~loc @@ E.Blk_error err in
          SD.return (bl, `any)
      in
      begin match islast with
        | `last ->
          let bl = {E.stmts=List.rev acc} in
          SD.return (bl, loc)
        | `any ->
          block_stmts ~notation (st::acc)
      end

  let meta_expr ~notation () : A.Meta_expr.t SD.t =
    SD.parsing (Error.wrap "parsing meta-expression") @@
    meta_expr_rec_ ~notation ()
end

module P_goal : sig
  val goal : notation:Notation.t -> unit -> A.Goal.t Parser.t
end = struct
  (* parse a sequent *)
  let goal ~notation () : A.Goal.t SD.t =
    let* loc1 = SD.loc in
    let* e = P_expr.expr ~ty_expect:A.Expr.bool ~notation () in
    (* TODO: read "new (x y:int)" *)
    (* TODO: read "assume expr" *)
    let+ loc2 = SD.loc in
    let loc = loc1 ++ loc2 in
    A.Goal.make ~loc ~hyps:[] e
end

module P_proof : sig
  val block : notation:Notation.t -> unit -> A.Proof.block Parser.t
  val proof : notation:Notation.t -> unit -> A.Proof.t Parser.t
end = struct

  let rec proof ~notation () : A.Proof.t SD.t =
    SD.switch_next @@ fun tok t_loc ->
    match tok with
    | SYM "exact" ->
      `consume,
      let* e = P_meta_expr.meta_expr ~notation () in
      let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after exact proof step") in
      let loc = t_loc ++ loc2 in
      A.Proof.exact ~loc e

    | SYM "by" ->
      `consume,
      let* e = P_meta_expr.meta_expr ~notation () in
      let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after exact proof step") in
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

  and block ~notation () : A.Proof.block SD.t =
    block_rec ~notation []

  and block_rec ~notation acc : A.Proof.block SD.t =
    SD.switch_next @@ fun tok t_loc ->
    match tok with
    | SYM "have" ->
      `consume,
      let* name = P_expr.p_const in
      let* () = SD.exact' EQDEF ~msg:(m_"expect `:=` after `have <name>`") in
      let* goal = P_goal.goal ~notation () in
      let* proof, loc2 = in_braces ~what:"`have` step" @@ block ~notation () in
      let loc = t_loc ++ loc2 in
      (* recurse *)
      block_rec ~notation (A.Proof.bl_have ~loc name goal proof :: acc)

    | LET ->
      `consume,
      let* var, var_loc = P_expr.p_ident in
      let var = A.Var.make ~kind:A.Var.V_normal ~loc:var_loc var None in
      let* () = SD.exact' EQDEF ~msg:(m_"expect `:=` after `let <name>`") in
      let* e = P_meta_expr.meta_expr ~notation () in
      let* loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after `let <name> := <expr>") in
      let loc = t_loc ++ loc2 in
      block_rec ~notation (A.Proof.bl_let ~loc var e :: acc)

    | SYM "pick" ->
      `consume,
      let* x, x_lock = P_expr.p_ident in
      let x = A.Var.make ~kind:A.Var.V_normal ~loc:x_lock x None in
      let* () = SD.exact' (SYM "where") ~msg:(m_"expect `where` after `pick <var>`") in
      let* cond = P_expr.expr ~notation () in
      let* proof, loc2 = in_braces ~what:"pick step" @@ block ~notation () in
      let loc = t_loc ++ loc2 in
      block_rec ~notation
        (A.Proof.bl_pick ~loc x cond proof :: acc)

    (* TODO: suffices *)

    | _ ->
      (* parse an atomic proof as the last step *)
      `keep,
      let* r = SD.try_ (proof ~notation ()) in
      begin match r with
        | Ok pr ->
          SD.return {A.Proof.steps=List.rev acc; qed=pr}

        | Error err ->
          let* _ = try_recover_semi in
          let* loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after a proof") in
          let loc = t_loc ++ loc2 in
          let pr = A.Proof.error ~loc err in
          SD.return {A.Proof.steps=List.rev acc; qed=pr}
      end
end

module P_top : sig
  type top_parser =
    loc0:Loc.t -> notation:Notation.t -> unit -> A.Top.t SD.t

  val parsers : (string * top_parser) list

  val top : notation:Notation.t -> unit -> A.Top.t option SD.t
end = struct
  type top_parser =
    loc0:Loc.t -> notation:Notation.t -> unit -> A.Top.t SD.t

  (* parse logic definition *)
  let p_def ~loc0 ~notation () : A.Top.t SD.t =
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
        let+ tok, t_loc = SD.next in
        tok, t_loc, Some e
      | _ ->
        SD.return (tok, t_loc, None)
    in
    if not (Token.equal tok EQDEF) then (
      SD.fail @@
      Error.makef ~loc:t_loc
        "expected `:=` in a definition after <vars> and optional return type,@ \
         got %a instead" Token.pp tok
    ) else (
      Log.debugf 5 (fun k->k"def: return type %a, %d vars"
                       (Fmt.Dump.option A.Expr.pp_quoted) ret (List.length vars));
      let* body = P_expr.expr ~notation () in
      let* loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `end` after a definition") in
      let loc = loc0 ++ loc2 in
      SD.return @@ A.Top.def ~loc name vars ret body
    )

  let p_declare ~loc0 ~notation () : A.Top.t SD.t =
    let* name = P_expr.p_const in
    let* () = SD.exact' COLON ~msg:(m_"expect `:` in a type declaration") in
    let* ty = P_expr.expr_atomic ~ty_expect:A.Expr.type_ ~notation () in
    Log.debugf 5 (fun k->k"parsed decl: type %a" A.Expr.pp ty);
    let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `end` after a declaration") in
    let loc = loc0 ++ loc2 in
    A.Top.decl ~loc name ty

  let p_show ~loc0 ~notation () : _ SD.t =
    let* e = P_expr.expr ~notation () in
    let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after `show <expr>`") in
    let loc = loc0 ++ loc2 in
    A.Top.show ~loc e

  let p_eval ~loc0 ~notation () : _ SD.t =
    let* e = P_meta_expr.meta_expr ~notation () in
    let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `;` after eval <expr>`") in
    let loc = loc0 ++ loc2 in
    A.Top.eval ~loc e

  let p_thm ~loc0 ~notation () : _ SD.t =
    let* name = P_expr.p_const in
    let* () = SD.exact' EQDEF ~msg:(m_"expect `:=` after the theorem's name") in
    let* goal = P_goal.goal ~notation () in
    let+ pr, loc2 =
      in_braces ~what:"theorem statement" @@ P_proof.block ~notation () in
    let loc = loc0 ++ loc2 in
    A.Top.theorem ~loc name goal pr

  let p_goal ~loc0 ~notation () : _ SD.t =
    let* goal = P_goal.goal ~notation () in
    let+ pr, loc2 =
      in_braces ~what:"goal statement" @@ P_proof.block ~notation () in
    let loc = loc0 ++ loc2 in
    A.Top.goal ~loc goal pr

  let p_fixity ~loc0 ~notation () : _ SD.t =
    let* name = P_expr.p_const in
    let* () = SD.exact' EQDEF ~msg:(m_"expect `:=` after symbol") in
    let* s, s_loc = P_expr.p_ident in
    let* mkfix, needsint =
      match s with
      | "infix" -> SD.return (Fixity.infix, true)
      | "prefix" -> SD.return (Fixity.prefix, true)
      | "postfix" -> SD.return (Fixity.postfix, true)
      | "lassoc" -> SD.return (Fixity.lassoc, true)
      | "rassoc" -> SD.return (Fixity.rassoc, true)
      | "binder" -> SD.return (Fixity.binder, true)
      | "normal" -> SD.return ((fun _->Fixity.normal), false)
      | _ ->
        SD.fail @@
        Error.makef ~loc:s_loc
          "expected one of: normal|infix|prefix|postfix|lassoc|rassoc|binder@ \
           but got '%s'" s
    in
    let* n =
      if needsint then (
        SD.switch_next @@ fun n _loc ->
        match n with
        | NUM n -> `consume, SD.return (int_of_string n)
        | _ -> `keep, SD.fail_str "expect a number after `fixity`"
      ) else SD.return 0
    in
    let fix = mkfix n in
    let+ loc2 = SD.exact SEMI_COLON ~msg:(m_"expect `end` after fixity declarations") in
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

  let top ~notation () : A.Top.t option SD.t =
    Log.debugf 1 (fun k->k"parse top");
    let errm ~loc tok =
      Error.makef ~loc
        "expected toplevel statement, but got token %a;@ expected one of: [%s]"
        Token.pp tok
        (String.concat "," @@ List.map (fun (s,_) -> String.escaped s) parsers)
    in
    let* loc0 = SD.loc in
    let* res =
      SD.try_ @@
      SD.switch_next @@ fun tok0 loc0 ->
      match tok0 with
      | EOF ->
        `keep, SD.return None
      | SYM s ->
        `consume,
        begin match List.assoc s parsers with
          | exception Not_found ->
            Log.debugf 5 (fun k->k"unknown toplevek tok %a" Token.pp tok0);
            let err = errm ~loc:loc0 tok0 in
            let* _ = try_recover_semi in
            let+ loc2 = SD.exact SEMI_COLON
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
        let+ loc2 = SD.exact SEMI_COLON
            ~msg:(m_"expect semicolon after a toplevel statement") in
        let loc = loc0 ++ loc2 in
        Some (A.Top.error ~loc err)
    in
    begin match res with
      | Ok r -> SD.return r
      | Error err ->
        Log.debugf 0 (fun k->k"error %a" Error.pp err);
        let* _ = try_recover_semi in
        let+ loc2 = SD.exact SEMI_COLON
            ~msg:(m_"expect semicolon after toplevel statement") in
        let loc = loc0 ++ loc2 in
        let err = Error.wrap ~loc "parsing a toplevel statement" err in
        Some (A.Top.error ~loc err)
    end
end

let parse_expr ~notation () : A.Expr.t SD.t =
*)

(* TODO
let top = P_top.top
   *)

let p_top_ _self = SD.fail "TODO: top"

let top self : A.Top.t SD.t =
  let+ st = p_top_ self in
  begin match st.A.view with
    | A.Top.Fixity {name; fixity} ->
      Notation.Ref.declare self.notation (A.Const.name name) fixity
    | _ -> ()
  end;
  st
