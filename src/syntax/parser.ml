

open Common_

module A = Parse_ast
module SD = Sexp_decode
module Sexp = Sexp_loc

open Loc.Infix
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

(** Parse a variable.
    @param p_ty how to parse the type, if needed
    @param require_ty if true, a type must be provided *)
let p_var ?(require_ty=false) ~p_ty () =
  let* v = SD.value in
  let loc = v.Sexp.loc in
  match v.Sexp.view with
  | Sexp.Atom name ->
    if require_ty then SD.fail "type annotation on the variable is required"
    else SD.return @@ A.Var.make ~loc name None
  | Sexp.Bracket_list [{Sexp.view=Sexp.Atom name; _}; ty]
  | Sexp.List [{Sexp.view=Sexp.Atom name; _}; ty] ->
    (* [x ty] is [x : ty] *)
    let+ ty = SD.sub p_ty ty in
    A.Var.make ~loc name (Some ty)
  (* TODO: parse as `$ (x : ty) $`
  | Sexp.Dollar _ ->
  *)
  | _ ->
    SD.fail "expected a variable"

let p_const =
  let+ loc = SD.loc
  and+ c = SD.atom in
  A.Const.make_str ~loc c

module P_expr : sig
  val p_var : ?require_ty:bool -> A.Expr.var parser
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
  let p_rec_ (self:t) : _ SD.t =
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
           let+ c = SD.sub p_const c in
           E.const ~loc c None

         | c :: args ->
           let+ c = SD.sub p_const c
           and+ args = SD.map_l (SD.sub expr) args in
           E.const ~loc c (Some args)
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

  let top self =
    let+ r = SD.try_catch (p_rec_ self) in
    match r with
    | Ok x -> x
    | Error err ->
      (* reify error *)
      let loc = SD.Err.loc err in
      let err = SD.Err.to_error err in
      E.error ~loc err

  let p_var ?require_ty self = p_var ?require_ty ~p_ty:(top self) ()
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
       let+ c = p_const in
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
  val var : A.Meta_expr.var parser
  val top : A.Meta_expr.t parser
end = struct
  module E = A.Meta_expr
  module Ty = A.Meta_ty

  (* parse a variable *)
  let var self : E.var SD.t = p_var ~p_ty:(P_meta_ty.top self) ()

  let rec meta_expr_rec_ (self:t) : E.t SD.t =
    SD.try_l ~msg:"expected a meta-expression" [

      (* value literals *)

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

      (* string literal *)
      (SD.is_quoted_str,
       let+ loc = SD.loc
       and+ s = SD.quoted_str in
       E.mk ~loc @@ E.Value (E.V_string s));

      (* unit: `()` *)
      (let emptyl =
         let+ l = SD.list in l==[]
       in
       SD.succeeds emptyl,
       let+ loc = SD.loc in
       E.mk ~loc @@ E.Value E.V_unit);

      (* block expression *)
      (SD.is_applied "do",
       let+ loc = SD.loc
       and+ stmts = SD.applied "do" (block_stmt self) in
       let bl = {E.stmts} in
       E.mk ~loc (E.Block_expr bl));

      (SD.is_brace_list,
       let+ loc = SD.loc
       and+ stmts = SD.brace_list_of ~what:"block statements" (block_stmt self) in
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

      (SD.is_applied "fn",
       let* loc = SD.loc
       and* l = SD.applied "fn" SD.value in
       begin match l with
         | args :: (_::_ as body_l) ->
           let+ args =
             SD.sub
               (SD.list_or_bracket_list_of ~what:"variables" (var self))
               args
           and+ body =
             SD.sub_l (block_stmt self) body_l
           in
           let body = {E.stmts=body} in
           E.mk ~loc @@ E.Fun (args, body)

         | _ ->
           let err = Error.make ~loc "expected `fn <vars> <body>`" in
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
       let+ x, e = SD.applied2 "let" (var self) (meta_expr_rec_ self) in
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

module P_goal : sig
  val top : A.Goal.t parser
end = struct
  type item =
    | Assume of A.Expr.t
    | Prove of A.Expr.t
    | New of A.Expr.var

  let p_item (self:t) : _ SD.t =
    SD.try_l ~msg:"goal item (assume|prove|new)" [
      (SD.is_applied "assume",
       let+ loc = SD.loc
       and+ e = SD.applied1 "assume" (P_expr.top self) in
       Assume e);

      (SD.is_applied "prove",
       let+ loc = SD.loc
       and+ e = SD.applied1 "prove" (P_expr.top self) in
       Prove e);

      (SD.is_applied "new",
       let+ loc = SD.loc
       and+ v = SD.applied1 "prove" (P_expr.p_var self) in
       New v);
    ]

  let top self =
    let+ loc = SD.loc
    and+ l = SD.applied "goal" (p_item self) in

    let assume = ref [] in
    let prove = ref [] in
    let new_ = ref [] in

    List.iter
      (function
        | Assume e -> assume := e :: !assume
        | Prove e -> prove := e :: !prove
        | New v -> new_ := v :: !new_)
      l;

    begin match !prove with
      | [p] ->
        A.Goal.goal ~loc ~hyps:!assume ~new_vars:!new_ p
      | [] ->
        let err = Error.make ~loc "a goal needs one `(prove <expr>)` entry" in
        A.Goal.error ~loc err
      | g1 :: g2 :: _ ->
        let loc_err = g1.loc ++ g2.loc in
        let err = Error.make ~loc:loc_err "a goal needs only one `(prove <expr>)` entry" in
        A.Goal.error ~loc err
    end
end

module P_proof : sig
  val block : A.Proof.block or_error parser
  val proof : A.Proof.t parser
end = struct
  module P = A.Proof

  let doc =
{|expected a proof.

Proofs can be of various forms:
- `(exact <meta-expr>)` evaluates the meta-expr (of type `thm`) to obtain a theorem.
- `(by <meta-expr> [<var>*])` applies the meta-expr
    (of type `thm list -> goal -> thm`)
    to the list of theorems (corresponding to previous
    steps), and to the current goal, to attempt to prove it.
- `(steps <step>+ (qed <proof>))` starts by proving a series of intermediate
  steps, and leverages them in the `qed` sub-proof to prove the goal.

  Each step can be one of:
  * `(have <name> <goal> <proof>)` to prove a sub-goal, and name it,
    so it can be accessed in the steps below. This is forward-chaining.
  * `(suffices <goal> <proof>)` to replace the current goal with
    a new one, along with a proof that the new goal implies the old one.
    This is backward chaining.
  * `(let <name> <meta-expr>)` to locally name a meta-value, which
    can then be reused in multiple steps below. This can in particular return
    a lemma or custom solver.
  * `(pick <var> <cond:expr> <proof>)` to introduce a new variable
    that satisfies `cond`, using the choice axiom and `select` construct.
    The proof is there to show that `cond` is satisfiable.
  * the last step is `(qed <proof>)` and must succeed in proving the current
    goal (the one from the last `suffices`, or the original goal otherwise.)
|}

  let p_var : P.proof_var SD.t = p_const

  type gen_step =
    | GS_goal of A.Goal.t
    | GS_block_elt of P.block_elt
    | GS_qed of P.t

  (* analyze a list of steps. It must contain at most one goal. *)
  let analyze_steps ~loc
      (l:gen_step list) : (A.Goal.t option * P.block, Error.t) result =
    let goal = ref [] in
    let steps = ref [] in
    let qed = ref [] in

    let classify = function
      | GS_goal g -> goal := g :: !goal
      | GS_block_elt s -> steps := s :: !steps
      | GS_qed p -> qed := p :: !qed
    in

    List.iter classify l;
    let steps = List.rev !steps in

    begin match !qed, !goal with
      | [qed], [] ->
        Ok (None, {P.steps; qed})
      | [qed], [g] ->
        Ok (Some g, {P.steps; qed})
      | [], _ ->
        Error(Error.make ~loc "expected a `qed` in the structured proof")
      | q1::q2::_, _ ->
        let loc = q1.loc ++ q2.loc in
        Error(Error.make ~loc "expected only one `qed` in the structured proof")
      | _, g1::g2::_ ->
        let loc = g1.loc ++ g2.loc in
        Error(Error.make ~loc "expected only one goal` in the structured proof")
    end

  (* require a goal, and steps, and return the corresponding proof *)
  let return_structured_step ~loc (l:gen_step list) : P.t =
    match analyze_steps ~loc l with
    | Ok (Some g, block) ->
      P.mk ~loc @@ P.Structured {goal=g; block}
    | Ok (None, _) ->
      let err = Error.make ~loc "no goal is present" in
      P.mk ~loc @@ P.Error err
    | Error err -> P.mk ~loc @@ P.Error err

  (* require no goal, and return the block *)
  let return_block ~loc (l:gen_step list) : P.block or_error =
    match analyze_steps ~loc l with
    | Ok (None, bl) -> Ok bl
    | Ok (Some g, _) ->
      let err = Error.make ~loc:g.loc "unexpected goal in this structured proof block" in
      Error (g.loc, err)
    | Error err -> Error (loc, err)

  (* parser for atomic proofs (i.e. leaves) *)
  let p_atomic self : P.t option SD.t =
    SD.try_l ~msg:"atomic proof" [

      (SD.is_applied "exact",
       let+ loc = SD.loc
       and+ e = SD.applied1 "exact" (P_meta_expr.top self) in
       Some (P.exact ~loc e));

      (SD.is_applied "by",
       let+ loc = SD.loc
       and+ e, vars =
         SD.applied2 "by" (P_meta_expr.top self)
           (SD.list_or_bracket_list_of ~what:"previous steps" p_var)
       in
       Some (P.by ~loc e vars));

    ] ~else_:(SD.return None)

  let (let*??) (x:('a, Loc.t * Error.t) result) f =
    match x with
    | Error (loc,err) ->
      SD.return @@ GS_block_elt (P.bl_error ~loc err)
    | Ok x -> f x

  let rec proof_rec_ (self:t) : P.t SD.t =
    let+ r =
      SD.try_catch @@
      let* a = p_atomic self in
      match a with
      | Some p -> SD.return p
      | None ->
        proof_structured_ self
    in
    match r with
    | Ok x -> x
    | Error err ->
      let loc = SD.Err.loc err and err = SD.Err.to_error err in
      P.error ~loc err (* reify error *)

  and proof_structured_ self =
    SD.with_msg ~msg:"parsing structured proof" @@
    SD.try_l ~msg:doc [

      (SD.is_applied "steps",
       let+ loc = SD.loc
       and+ l = SD.applied "steps" (proof_step_ self) in
       return_structured_step ~loc l
      );

      (SD.is_brace_list,
       let+ loc = SD.loc
       and+ l = SD.brace_list_of ~what:"proof steps" (proof_step_ self) in
       return_structured_step ~loc l);

    ] ~else_:(
      let+ loc = SD.loc in
      let err = Error.make ~loc doc in
      P.error ~loc err
    )

  (* read a proof block *)
  and proof_block (self:t) : (P.block, Loc.t * Error.t) result SD.t =
    let* loc = SD.loc in
    let+ l = SD.list_or_bracket_list_of ~what:"proof steps" (proof_step_ self) in
    return_block ~loc l

  (* parse an individual step in a structured block *)
  and proof_step_ (self:t) : gen_step SD.t =
    SD.try_l ~msg:"expected a proof step, `(qed <proof>)`, or `(goal <proof>)`" [

      (SD.is_applied "qed",
       let+ loc = SD.loc
       and+ p = SD.applied1 "qed" (proof_rec_ self) in
       GS_qed p);

      (SD.is_applied "goal",
       let+ loc = SD.loc
       and+ g = SD.applied1 "goal" (P_goal.top self) in
       GS_goal g);

      (SD.is_applied "let",
       let+ loc = SD.loc
       and+ var, rhs = SD.applied2 "let" (P_meta_expr.var self) (P_meta_expr.top self) in
       let step = P.bl_let ~loc var rhs in
       GS_block_elt step);

      (SD.is_applied "pick",
       let* loc = SD.loc
       and* var, cond, proof = SD.applied3 "pick"
           (P_expr.p_var self) (P_expr.top self) (proof_block self) in
       let*?? bl = proof in
       let step = P.bl_pick ~loc var cond bl in
       SD.return @@ GS_block_elt step);

      (SD.is_applied "have",
       let* loc = SD.loc
       and* var, goal, proof = SD.applied3 "have"
           p_var (P_goal.top self) (proof_block self) in
       let*?? bl = proof in
       let step = P.bl_have ~loc var goal bl in
       SD.return @@ GS_block_elt step);

      (SD.is_applied "pick",
       let* loc = SD.loc
       and* var, cond, proof = SD.applied3 "pick"
           (P_expr.p_var self) (P_expr.top self) (proof_block self) in
       let*?? bl = proof in
       let step = P.bl_pick ~loc var cond bl in
       SD.return @@ GS_block_elt step);

    ]

  let proof self =
    SD.with_msg ~msg:"parsing a proof" @@ proof_rec_ self
  let block self =
    SD.with_msg ~msg:"parsing a proof block" @@
    proof_block self
end

module P_top : sig
  type top_parser = A.Top.t parser

  val parsers : (string * top_parser) list

  val top : A.Top.t parser
end = struct
  type top_parser = A.Top.t parser

  let ( let*? ) e f = match e with
    | Ok x -> f x
    | Error (loc,err) ->
      SD.return @@ A.Top.error ~loc err

  (* parse logic definition *)
  let p_def (self:t) : A.Top.t SD.t =
    let* loc = SD.loc in
    let+ name, vars, ret, body =
      SD.applied4 "def" p_const
        (SD.list_or_bracket_list_of ~what:"variables"
           (P_expr.p_var ~require_ty:true self))
        (P_expr.top self)
        (P_expr.top self)
    in
    A.Top.def ~loc name vars (Some ret) body

  let p_declare self : A.Top.t SD.t =
    let* loc = SD.loc in
    let+ name, ty = SD.applied2 "decl" p_const (P_expr.top self) in
    A.Top.decl ~loc name ty

  let p_show self : _ SD.t =
    let* loc = SD.loc in
    let+ e = SD.applied1 "show" (P_expr.top self) in
    A.Top.show ~loc e

  let p_eval self : _ SD.t =
    let* loc = SD.loc in
    let+ e = SD.applied1 "eval" (P_meta_expr.top self) in
    A.Top.eval ~loc e

  let p_thm self : _ SD.t =
    let* loc = SD.loc in
    let* name, goal, proof =
      SD.applied3 "theorem"
        p_const (P_goal.top self) (P_proof.block self)
    in
    let*? bl = proof in
    SD.return @@ A.Top.theorem ~loc name goal bl

  let p_goal self : _ SD.t =
    let* loc = SD.loc in
    let* goal, proof =
      SD.applied2 "goal" (P_goal.top self) (P_proof.block self) in
    let*? bl = proof in
    SD.return @@ A.Top.goal ~loc goal bl

  let p_fixity self : _ SD.t =
    let* loc = SD.loc in

    let p_fix =
      let* loc = SD.loc
      and* s = SD.value in
      match s.Sexp_loc.view with
      | Sexp_loc.Atom "normal" -> SD.return Fixity.normal
      | Sexp_loc.List [a; n] ->
        let* a = SD.sub SD.atom a
        and* n = SD.sub SD.int n in
        begin match a with
          | "infix" -> SD.return (Fixity.infix n)
          | "prefix" -> SD.return (Fixity.prefix n)
          | "postfix" -> SD.return (Fixity.postfix n)
          | "lassoc" -> SD.return (Fixity.lassoc n)
          | "rassoc" -> SD.return (Fixity.rassoc n)
          | "binder" -> SD.return (Fixity.binder n)
          | _ -> SD.failf (fun k->k"unknown fixity `%s`" a)
        end
      | _ -> SD.fail "expected a fixity"
    in
    let+ name, fix = SD.applied2 "fixity" p_const p_fix in
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

  let top (self:t) : A.Top.t SD.t =
    Log.debugf 1 (fun k->k"parse top");

    let* loc = SD.loc in
    let+ r =
      SD.try_catch @@
      SD.with_msg ~msg:"parsing toplevel statement" @@
      let* v = SD.value in
      match v.Sexp_loc.view with
      | Sexp_loc.List ({Sexp_loc.view=Atom s;_} :: l) ->
        begin match List.assoc_opt s parsers with
          | None ->
            SD.failf (fun k->k"unknown command %S" s)
          | Some p ->
            SD.with_msg ~msg:(spf "parsing command %S" s) @@
            p self
        end
      | _ -> SD.fail "expected a top statement: `(<command> <arg>*)`"
    in

    begin match r with
      | Ok x -> x
      | Error err ->
        let loc = SD.Err.loc err and err = SD.Err.to_error err in
        A.Top.error ~loc err
    end
end

let p_top_ = P_top.top

let top self : A.Top.t SD.t =
  let+ st = p_top_ self in
  begin match st.A.view with
    | A.Top.Fixity {name; fixity} ->
      Notation.Ref.declare self.notation (A.Const.name name) fixity
    | _ -> ()
  end;
  st
