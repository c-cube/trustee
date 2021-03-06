module K = Trustee_core.Kernel
module Notation = Notation
module E = K.Expr

open OUnit2

(*$inject
  open Sigs
  let notation = Notation.Ref.of_notation Notation.empty_hol

  let() = K.__pp_ids := true

  module E = K.Expr
  module Make() = struct
    let ctx = K.Ctx.create ()
    let env = A.Env.create ~fixity:(Notation.Ref.find_or_default notation) ()
    let bool = K.Expr.bool ctx
    let c_bool = K.Const.bool ctx
    let type_ = K.Expr.type_ ctx
    let tau = K.Expr.const ctx (K.Expr.new_ty_const ctx "tau" 0) []
    let lambda v t = K.Expr.lambda ctx v t
    let v' s ty = K.Var.make s ty
    let v x = K.Expr.var ctx x
    let (@->) a b = K.Expr.arrow ctx a b
    let (@@) a b = K.Expr.app ctx a b
    let new_const ctx s ty = K.Expr.new_const ctx s [] ty
    let const c = K.Expr.const ctx c []
    let a = new_const ctx "a0" tau
    let b = new_const ctx "b0" tau
    let c = new_const ctx "c0" tau
    let f1 = new_const ctx "f1" (tau @-> tau)
    let g1 = new_const ctx "g1" (tau @-> tau)
    let h1 = new_const ctx "h1" (tau @-> tau)
    let f2 = new_const ctx "f2" (tau @-> tau @-> tau)
    let g2 = new_const ctx "g2" (tau @-> tau @-> tau)
    let h2 = new_const ctx "h2" (tau @-> tau @-> tau)
    let p0 = new_const ctx "p0" bool
    let q0 = new_const ctx "q0" bool
    let r0 = new_const ctx "r0" bool
    let p1 = new_const ctx "p1" (tau @-> bool)
    let q1 = new_const ctx "q1" (tau @-> bool)
    let r1 = new_const ctx "r1" (tau @-> bool)
    let p2 = new_const ctx "p2" (tau @-> tau @-> bool)
    let q2 = new_const ctx "q2" (tau @-> tau @-> bool)
    let r2 = new_const ctx "r2" (tau @-> tau @-> bool)
    let forall = K.Expr.new_const ctx "!" [] ((tau @-> bool) @-> bool)
    let() = Notation.Ref.declare notation "!" (F_binder 10)
    let plus = K.Expr.new_const ctx "+" [] (tau @-> tau @-> tau)
    let eq = K.Const.eq ctx
    let() = Notation.Ref.declare notation "+" (F_right_assoc 20)

    let of_str s = Syntax.parse_expr_infer ~env (Lexer.create ~file:"" s)
  end

  module M = Make()
  module AE = Parse_ast.Expr
  module A = struct
    include Parse_ast
    include AE
    let loc = Loc.none
    let v (s:string) : t = var ~loc (A.Var.make ~loc s None)
    let vv s : A.var = A.Var.make ~loc s None
    let of_str s : AE.t = Syntax.parse_expr ~env:M.env (Lexer.create ~file:"" s)
    let let_ = let_ ~loc
    let ty_arrow = ty_arrow ~loc
    let eq = eq ~loc
    let of_expr = of_k_expr ~loc
    let b_forall vars (bod:AE.t) : AE.t =
      AE.bind ~loc ~b_loc:loc (AE.of_k_const ~loc M.forall)
        (List.map (fun (x,ty)-> A.Var.make ~loc x ty) vars) bod
    let c x : t = AE.of_k_const ~loc x
    let (@->) a b = AE.ty_arrow ~loc a b
    let (@) a b = AE.app_l a b
  end
  open A

  let parse_e s : K.Expr.t =
    Syntax.parse_expr_infer ~ctx:M.ctx ~env:M.env (Lexer.create ~file:"" s)
*)

(* test printer itself *)
(*$= & ~printer:Fmt.(to_string (within "`" "`" A.pp)) ~cmp:(fun x y->A.to_string x=A.to_string y)
  A.(v "f" @ [v "x"]) (A.of_str "(f x)")
  A.(v "f" @ [v "x"]) (A.of_str "f x")
  A.(b_forall ["x", None; "y", None] (c M.p1 @ [v "x"])) \
    (A.of_str "!x y. p1 x")
  A.(b_forall ["x", Some (v "A")] (c M.p1 @ [c M.f1 @ [v "x"]])) \
    (A.of_str "!x:A. p1 (f1 x)")
  A.(b_forall ["x", Some (v "A"); "y", Some (v "A")] (c M.p1 @ [c M.f1 @ [v "x"]])) \
    (A.of_str "!x y:A. p1 (f1 x)")
  A.(b_forall ["x", Some (v "A"); "y", Some (v "B")] (c M.p1 @ [c M.f1 @ [v "x"]])) \
    (A.of_str "!(x:A) (y:B). p1 (f1 x)")
  A.(c M.plus @ [v "x"; v "y"]) (A.of_str "x + y")
  A.(c M.plus @ [v "x"; c M.plus @ [v "y"; v "z"]]) (A.of_str "x + y + z")
  A.(let_ [vv"x", c M.a] (c M.p1 @ [v "x"])) (A.of_str "let x := a0 in p1 x")
  A.(let_ [vv"x", c M.a; vv"y", c M.b] (c M.p2 @ [v "x"; v"y"])) \
    (A.of_str "let x:=a0 and y:=b0 in p2 x y")
  A.(ty_arrow (v"a")(v"b")) (A.of_str "a->b")
  A.(eq (v"a")(v"b")) (A.of_str "a = b")
  A.(b_forall ["x", Some (c M.a @-> c M.b @-> c M.c)] (A.eq (v"x")(v"x"))) \
    (A.of_str "! (x:a0->b0->c0). x=x")
    A.(lambda ~loc [A.Var.make ~loc "x" @@ Some (c M.a @-> c M.b @-> c M.c)] \
         (A.eq (v"x")(v"x"))) \
    (A.of_str "\\ (x:a0->b0->c0). x=x")
  A.(c M.eq) (A.of_str "(=)")
  A.(c M.c_bool) (A.of_str "bool")
  A.(eq (c M.p2 @ [v "x"; v "y"]) (c M.q2 @ [v "y"; v "x"])) \
    (A.of_str "p2 x y = q2 y x")
*)

(* FIXME: reinstate that, after we declare symbols properly to the type env
(* test type inference *)
(*     $= & ~cmp:E.equal ~printer:E.to_string
  M.(tau @-> tau) (K.Const.ty M.f1)
  M.(const f1 @@ v (v' "a" tau)) (parse_e "f1 a")
*)
   *)

(* test lexer *)
(*$inject
  module Fmt = CCFormat
  let lex_to_list s =
    let lex = Lexer.create ~file:"" s in
    Lexer.S.to_list lex

  let str_tok_to_l = Fmt.(to_string @@ Dump.list Token.pp)
*)

(*$= & ~printer:str_tok_to_l
    [ SYM("foo"); \
      SYM("+"); \
      WILDCARD; \
      SYM("bar13"); \
      LPAREN; \
      SYM("hello"); \
      SYM("!"); \
      EQDEF; \
      QUOTED_STR(" co co"); \
      END; \
      QUOTE_STR "a"; \
      SYM("world"); \
      RPAREN; \
      EOF; \
    ] \
    (lex_to_list {test| foo + _ bar13(hello! := " co co" end 'a world) |test})
    [ LPAREN; \
      LPAREN; \
      NUM("12"); \
      SYM("+"); \
      END; \
      SYM("f"); \
      LPAREN; \
      SYM("x"); \
      COMMA; \
      COLON; \
      IN; \
      QUESTION_MARK_STR("a"); \
      QUESTION_MARK; \
      QUESTION_MARK; \
      SYM("b"); \
      SEMI_COLON; \
      SYM("Y"); \
      SYM("\\"); \
      LPAREN; \
      RPAREN; \
      RPAREN; \
      SYM("---"); \
      LET; \
      BY; \
      SYM("z"); \
      RPAREN; \
      SYM("wlet"); \
      RPAREN; \
      EOF; \
    ] \
    (lex_to_list {test|((12+end f(x, : in ?a ? ? b; Y \( ))---let by z)wlet)|test})
  [EOF] (lex_to_list "  ")
*)

let suite =
  "syntax" >::: [
  ]
