

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
  val p_var : A.Expr.var parser
  val top : A.Expr.t parser
end = struct
  module E = A.Expr

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
    SD.try_l ~msg:doc [

      (SD.is_atom_of "expr/type", SD.return E.type_);

      (SD.is_applied "expr/app",
       let* l = SD.applied "expr/app" SD.value in
       begin match l with
         | [] | [_] -> SD.fail "expr/app needs at least 2 arguments"
         | f :: args ->
           let+ f = SD.sub expr f
           and+ args = SD.map_l (SD.sub expr) args in
           E.app f args
       end);

      (SD.is_applied "expr/arrow",
       let* loc = SD.loc in
       let* l = SD.applied "expr/arrow" SD.value in
       begin match l with
         | [] | [_] -> SD.fail "expr/arrow needs at least 2 arguments"
         | l ->
           let+ l = SD.map_l (SD.sub expr) l in
           match List.rev l with
           | ret :: args -> E.ty_arrow ~loc (List.rev args) ret
           | [] -> assert false
       end);

      (SD.is_applied "expr/lam",
       let* loc = SD.loc in
       let+ vars, bod =
         SD.applied2 "expr/lam"
           SD.(list_of ~what:"typed variables" @@ p_var ~p_ty:expr ()) expr in
       E.lambda ~loc vars bod);

      (SD.is_applied "expr/var",
       let* loc = SD.loc in
       let+ v = SD.applied1 "expr/var" (p_var ~p_ty:expr ()) in
       E.var ~loc v);

      (SD.is_applied "expr/const",
       let* loc = SD.loc in
       let* l = SD.applied "expr/const" SD.value in
       begin match l with
         | [] -> SD.fail "expr/const needs at least one argument"
         | [c] ->
           let+ c = SD.sub SD.atom c in
           E.const ~loc (A.Const.make ~loc (Name.make c)) None

         | c :: args ->
           let+ c = SD.sub SD.atom c
           and+ c_loc = SD.sub SD.loc c
           and+ args = SD.map_l (SD.sub expr) args in
           E.const ~loc (A.Const.make ~loc:c_loc (Name.make c)) (Some args)
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
           let expr = E.error ~loc err in
           SD.return expr
       end);

    ] ~else_:(
      let+ loc = SD.loc in
      let err = Error.make ~loc doc in
      E.error ~loc err
    )

  let p_var self = p_var ~p_ty:(top self) ()
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

module P_meta_ty : sig
  val top : A.Meta_ty.t parser
end = struct
  module Ty = A.Meta_ty

  let ty_rec (self:t) : _ SD.t =
    SD.fix @@ fun ty ->
    SD.try_l ~msg:"expected meta-level type" [

      (SD.is_atom,
       let+ loc = SD.loc
       and+ c = SD.atom in
       let c = A.Const.make ~loc (Name.make c) in
       Ty.const c);

      (SD.is_applied "->",
       let* loc = SD.loc in
       let* args = SD.applied "->" ty in
       match List.rev args with
       | ret :: (_ :: _ as rargs) ->
         SD.return @@ Ty.arrow (List.rev rargs) ret

       | _ ->
         let err = Error.make ~loc "`->` takes at least 2 arguments" in
         SD.return @@ Ty.mk ~loc @@ Ty.Error err);
    ] ~else_:(
      let+ loc = SD.loc in
      let err = Error.make ~loc "expected a meta-type" in
      Ty.mk ~loc @@ Ty.Error err
    )


  let top self : _ SD.t =
    SD.with_msg ~msg:"parsing a meta-type" @@ ty_rec self
end

module P_meta_expr : sig
  val top : A.Meta_expr.t parser
end = struct
  module E = A.Meta_expr
  module Ty = A.Meta_ty

  (* parse a variable *)
  let p_var self : E.var SD.t = p_var ~p_ty:(P_meta_ty.top self) ()

  let rec meta_expr_rec_ (self:t) : E.t SD.t =
    SD.try_l ~msg:"expected a meta-expression" [

      (SD.succeeds SD.int,
       let+ loc = SD.loc
       and+ i = SD.int in
       E.mk ~loc @@ E.Value (E.V_int i));

      (SD.is_atom_of "true",
       let+ loc = SD.loc in
       E.mk ~loc @@ E.Value (E.V_bool true));

      (SD.is_atom_of "false",
       let+ loc = SD.loc in
       E.mk ~loc @@ E.Value (E.V_bool false));

      (SD.is_quoted_str,
       let+ loc = SD.loc
       and+ s = SD.quoted_str in
       E.mk ~loc @@ E.Value (E.V_string s));

      (SD.is_applied "do",
       (* parse a block *)
       let+ loc = SD.loc
       and+ stmts = SD.applied "do" (block_stmt self) in
       let bl = {E.stmts} in
       E.mk ~loc (E.Block_expr bl));

      (SD.is_bracket_list,
       (* TODO: comprehensions, maybe
          "[for <var:string> <src:expr> <yield:expr> [if <guard:expr>]]"? *)
       let+ loc = SD.loc
       and+ l = SD.bracket_list_of ~what:"meta-expressions" (meta_expr_rec_ self) in
       E.mk ~loc (E.List_lit l));

      (SD.is_dollar_str,
       let* loc = SD.loc in
       (* parse $ … $ as a logic expression *)
       let+ e = P_expr.top self in
       E.mk ~loc (E.Expr_lit e));

      (SD.is_applied "if",
       let+ loc = SD.loc
       and+ e = SD.list_of ~what:"meta-expressions" (meta_expr_rec_ self) in
       begin match e with
         | [cond; a; b] ->
           E.mk ~loc @@ E.If (cond, a, Some b)
         | [cond; a] ->
           E.mk ~loc @@ E.If (cond, a, None)
         | _ ->
           let err = Error.make ~loc "`if` takes 2 or 3 arguments" in
           E.mk ~loc @@ E.Error err
       end);

      (SD.is_applied "cond",
       let* loc = SD.loc
       and* l = SD.list in

       begin match List.rev l with
         | last :: (_ :: _ as rl) ->
           let p_pair =
             SD.pair (meta_expr_rec_ self) (meta_expr_rec_ self)
           and p_default =
             SD.pair
               (SD.atom |> SD.guard ~msg:"expected `default`" (String.equal "default"))
               (meta_expr_rec_ self)
           in
           let+ cases =
             SD.with_msg ~msg:"parsing pairs of (<condition> <expression>)" @@
             SD.sub_l p_pair (List.rev rl)
           and+ default =
             let+ _, e = SD.sub p_default last in
             e
           in
           E.mk ~loc @@ E.Cond {cases; default}
         | _ ->
           let err = Error.make ~loc "`cond` requires at least a case and a default" in
           SD.return @@ E.mk ~loc @@ E.Error err
       end);

      (* variable *)
      (SD.is_atom,
       let+ loc = SD.loc
       and+ v = SD.atom in
       E.mk ~loc @@ E.Var (A.Var.make ~loc v None));

      (* application *)
      (SD.is_list,
       let+ loc = SD.loc
       and+ args = SD.list_of ~what:"meta-expressions" (meta_expr_rec_ self) in
       begin match args with
         | [] | [_] ->
           let err = Error.make ~loc "function application takes at least 2 arguments" in
           E.mk ~loc @@ E.Error err
         | f :: args ->
           E.mk ~loc @@ E.App (f, args)
       end);
    ] ~else_:(
      let+ loc = SD.loc in
      let err = Error.make ~loc "expected a meta-expression" in
      E.mk ~loc @@ E.Error err
    )

  and block_stmt (self:t) : E.block_stmt SD.t =
    SD.try_l ~msg:"expected a block statement (let|return|<expr>)" [

      (SD.is_applied "let",
       let* loc = SD.loc in
       let+ x, e = SD.applied2 "let" (p_var self) (meta_expr_rec_ self) in
       E.mk_bl ~loc @@ E.Blk_let (x, e));

      (SD.is_applied "return",
       let+ loc = SD.loc
       and+ e = meta_expr_rec_ self in
       E.mk_bl ~loc @@ E.Blk_return e);

    ] ~else_:(
      (* fallback case is to just eval an expression *)
      let+ loc = SD.loc
      and+ e = meta_expr_rec_ self in
      E.mk_bl ~loc @@ E.Blk_eval e
    )

  let top (self:t) : A.Meta_expr.t SD.t =
    SD.with_msg ~msg:"parsing meta-expression" @@
    meta_expr_rec_ self
end

(* TODO
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
