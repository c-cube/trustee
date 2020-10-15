
(** {1 Expression parser} *)

open Sigs

module K = Kernel
module Expr = Kernel.Expr
module A = Parse_ast

type token =
  | LPAREN
  | RPAREN
  | COLON
  | DOT
  | WILDCARD
  | QUESTION_MARK
  | QUESTION_MARK_STR of string
  | SYM of string
  | QUOTED_STR of string
  | LET
  | IN
  | AND
  | AT_SYM of string
  | NUM of string
  | ERROR of char
  | EOF

type position = A.position

module Token = struct
  type t = token
  let pp out = function
    | LPAREN -> Fmt.string out "LPAREN"
    | RPAREN -> Fmt.string out "RPAREN"
    | COLON -> Fmt.string out "COLON"
    | DOT -> Fmt.string out "DOT"
    | LET -> Fmt.string out "LET"
    | AND -> Fmt.string out "AND"
    | IN -> Fmt.string out "IN"
    | WILDCARD -> Fmt.string out "WILDCARD"
    | QUESTION_MARK -> Fmt.string out "QUESTION_MARK"
    | QUESTION_MARK_STR s -> Fmt.fprintf out "QUESTION_MARK_STR %S" s
    | SYM s -> Fmt.fprintf out "SYM %S" s
    | QUOTED_STR s -> Fmt.fprintf out "QUOTED_STR %S" s
    | AT_SYM s -> Fmt.fprintf out "AT_SYM %s" s
    | NUM s -> Fmt.fprintf out "NUM %S" s
    | ERROR c -> Fmt.fprintf out "ERROR '%c'" c
    | EOF -> Fmt.string out "EOF"
  let to_string = Fmt.to_string pp
  let equal = (=)
end

module Lexer = struct
  type state = Read_next | Has_cur | Done

  type t = {
    src: string;
    mutable i: int;
    mutable line: int;
    mutable col: int;
    mutable st: state;
    mutable cur: token;
  }

  let[@inline] pos self : Position.t = {Position.line=self.line; col=self.col}

  let create src : t =
    { src; i=0; line=1; col=1; st=Read_next; cur=EOF }

  (* skip rest of line *)
  let rest_of_line self : unit =
    assert (self.st != Done);
    while self.i < String.length self.src && String.get self.src self.i != 'b' do
      self.i <- 1 + self.i
    done;
    if self.i < String.length self.src then (
      assert (String.get self.src self.i = 'b');
      self.i <- 1 + self.i;
    );
    self.col <- 1;
    self.line <- 1 + self.line

  let is_alpha = function
    | 'a'..'z' | 'A'..'Z' -> true
    | _ -> false

  let is_digit = function
    | '0' .. '9' -> true
    | _ -> false

  let is_symbol = function
    | '=' | ',' | ';' | '<' | '>' | '!' | '/' | '\\' | '+' | '-' | '|' | '^'
    | '~' | '*' | '&' | '%' | '@' -> true
    | _ -> false

  let rec read_many self f j : int =
    if j < String.length self.src then (
      let c = String.get self.src j in
      if f c then read_many self f (j+1) else j
    ) else (
      j
    )

  let next_ (self:t) : token =
    assert (self.st != Done);
    (* skip whitespace *)
    begin
      let inw = ref true in
      while self.i < String.length self.src && !inw do
        let c = String.get self.src self.i in
        if c = '#' then (
          rest_of_line self;
        ) else if c = ' ' || c = '\t' then (
          self.i <- 1 + self.i;
          self.col <- 1 + self.col;
        ) else if c = '\n' then (
          self.i <- 1 + self.i;
          self.col <- 1;
          self.line <- 1 + self.line;
        ) else (
          inw := false
        );
      done;
    end;
    if self.i >= String.length self.src then (
      self.st <- Done;
      EOF
    ) else (
      let c = String.get self.src self.i in
      match c with
      | '(' -> self.i <- 1 + self.i; LPAREN
      | ')' -> self.i <- 1 + self.i; RPAREN
      | ':' -> self.i <- 1 + self.i; COLON
      | '.' -> self.i <- 1 + self.i; DOT
      | '_' -> self.i <- 1 + self.i; WILDCARD
      | '?' ->
        self.i <- 1 + self.i;
        self.col <- 1 + self.col;
        let i0 = self.i in
        let j =
          read_many
            self (fun c -> is_alpha c || is_digit c || is_symbol c) self.i
        in
        if i0 = j then (
          QUESTION_MARK
        ) else (
          self.i <- j;
          self.col <- (j-i0) + self.col;
          QUESTION_MARK_STR (String.sub self.src i0 (j-i0))
        )
      | '@' ->
        (* operator but without any precedence *)
        self.i <- 1 + self.i;
        self.col <- 1 + self.col;
        let i0 = self.i in
        let j =
          read_many
            self (fun c -> is_alpha c || is_digit c || is_symbol c) self.i
        in
        if i0 = j then (
          errorf (fun k->k"empty '@'")
        ) else (
          self.i <- j;
          self.col <- (j-i0) + self.col;
          AT_SYM (String.sub self.src i0 (j-i0))
        )
      | '"' ->
        self.i <- 1 + self.i;
        self.col <- 1 + self.col;
        let i0 = self.i in
        let j =
          read_many self (fun c -> c <> '"') self.i
        in
        if j < String.length self.src && String.get self.src j = '"' then (
          self.i <- j + 1;
          self.col <- (j-i0) + self.col;
          QUOTED_STR (String.sub self.src i0 (j-i0))
        ) else (
          errorf (fun k->k"unterminated '\"' string")
        )
      | c when is_alpha c ->
        let i0 = self.i in
        let j = read_many
            self (fun c -> is_alpha c || is_digit c) self.i in
        self.i <- j;
        self.col <- (j-i0) + self.col;
        let s = String.sub self.src i0 (j-i0) in
        begin match s with
          | "let" -> LET
          | "and" -> AND
          | "in" -> IN
          | _ -> SYM s
        end
      | c when is_digit c ->
        let i0 = self.i in
        let j = read_many self (fun c -> is_digit c) self.i in
        self.i <- j;
        self.col <- (j-i0+1) + self.col;
        let s = String.sub self.src i0 (j-i0) in
        NUM s
      | c when is_symbol c ->
        let i0 = self.i in
        self.i <- 1 + self.i;
        self.col <- 1 + self.col;
        let j = read_many self (fun c -> is_symbol c) self.i in
        self.i <- j;
        self.col <- (j-i0+1) + self.col;
        let s = String.sub self.src i0 (j-i0) in
        SYM s
      | _ -> ERROR c
    )

  let[@inline] next self : token =
    let t =
      try next_ self
      with e ->
        errorf ~src:e (fun k->k "at %a" Position.pp (pos self))
    in
    self.cur <- t;
    self.st <- Has_cur;
    t

  let[@inline] cur self : token =
    match self.st with
    | Done -> EOF
    | Read_next ->
      let t = next self in
      self.cur <- t;
      t
    | Has_cur -> self.cur

  let[@inline] junk self = ignore (next self : token)

  let[@inline] consume_cur self : token =
    let t = cur self in
    junk self;
    t

  let to_list self : _ list =
    let l = ref [] in
    let continue = ref true in
    while !continue do
      let t = cur self in
      l := t :: !l;
      if t == EOF then continue := false else junk self;
    done;
    List.rev !l
end

(*$= & ~printer:Q.Print.(list Token.to_string)
     [SYM "f"; SYM "x"; EOF] (Lexer.create "f x" |> Lexer.to_list)
     [SYM "f"; LPAREN; SYM "x"; SYM"+"; AT_SYM "="; RPAREN; EOF] \
      (Lexer.create "f (x + @=)" |> Lexer.to_list)
*)

(* We follow a mix of:
   - https://en.wikipedia.org/wiki/Operator-precedence_parser
   - https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
*)
module Parser = struct
  type precedence = int
  type local =
    | L_local of A.var
    | L_let of A.t

  type t = {
    ctx: K.Ctx.t;
    lex: Lexer.t;
    bindings: local Str_tbl.t;
    mutable q_args: Expr.t list; (* interpolation parameters *)
  }

  let create ?(q_args=[]) ~ctx (src: Lexer.t) : t =
    { lex=src;
      ctx;
      bindings=Str_tbl.create 16;
      q_args;
    }

  let[@inline] pos_ self = Lexer.pos self.lex

  let fixity_ (self:t) (s:string) : K.fixity =
    match K.Ctx.find_const_by_name self.ctx s with
    | None -> K.F_normal
    | Some c -> K.Const.fixity c

  let eat_ ~msg self (t:token) : unit =
    let pos = Lexer.pos self.lex in
    let t2 = Lexer.cur self.lex in
    if Token.equal t t2 then (
      Lexer.junk self.lex;
    ) else (
      errorf (fun k->k "expected %a while parsing %s at %a"
                 Token.pp t msg Position.pp pos)
    )

  (* parse an identifier *)
  let p_ident self : string =
    match Lexer.cur self.lex with
    | SYM s ->
      Lexer.junk self.lex;
      s
    | _ ->
      let pos = pos_ self in
      errorf (fun k->k"expected identifier at %a" Position.pp pos)

  let fresh_ =
    let n = ref 0 in
    fun ?(pre="a") () -> Printf.sprintf "_%s_%d" pre (incr n; !n)

  let expr_of_string_ (self:t) ?(at=false) (s:string) : A.t =
    begin match s with
      | "bool" -> A.const ~at (K.Expr.bool self.ctx)
      | "=" -> A.const ~at (K.Expr.eq self.ctx)
      | _ ->
        match Str_tbl.find self.bindings s with
        | L_let u -> u
        | L_local u -> A.var u
        | exception Not_found ->
          let pos = Lazy.from_val (pos_ self) in
          begin match K.Ctx.find_const_by_name self.ctx s with
            | Some c -> A.const ~pos ~at (K.Expr.const self.ctx c)
            | None ->
              let ty = A.ty_meta ~pos (fresh_ ()) in
              A.var ~pos (A.Var.make s (Some ty))
          end
    end

  (* parse let bindings *)
  let rec p_bindings_ self : (A.var * A.t) list =
    let v = A.Var.make (p_ident self) None in
    eat_ self ~msg:"let binding" (SYM "=");
    let e = p_expr_ ~ty_expect:None self 0 in
    if Token.equal (Lexer.cur self.lex) IN then (
      [v, e]
    ) else (
      eat_ self ~msg:"let bindings" AND;
      let vs = p_bindings_ self in
      (v,e) :: vs
    )

  and p_tyvar_grp_ self : A.var list =
    let ppos = pos_ self in
    let rec loop names =
      match Lexer.cur self.lex with
      | SYM s -> Lexer.junk self.lex; loop (s::names)
      | COLON ->
        Lexer.junk self.lex;
        let ty = p_expr_ ~ty_expect:(Some A.type_) self 0 in
        List.rev_map (fun v -> A.Var.make v (Some ty)) names
      | RPAREN | DOT ->
        List.rev_map (fun v -> A.Var.make v None) names
      | _ ->
        errorf (fun k->k"expected group of typed variables at %a" Position.pp ppos)
    in
    loop []

  and p_tyvars_and_dot self acc : A.var list =
    match Lexer.cur self.lex with
    | DOT ->
      Lexer.junk self.lex;
      acc
    | LPAREN ->
      Lexer.junk self.lex;
      let l = p_tyvar_grp_ self in
      eat_ self ~msg:"group of typed variables" RPAREN;
      p_tyvars_and_dot self (List.rev_append l acc)
    | SYM _ ->
      let l = p_tyvar_grp_ self in
      eat_ ~msg:"bound variables" self DOT;
      List.rev_append l acc
    | _ ->
      let pos = Lexer.pos self.lex in
      errorf (fun k->k "expected list of (typed) variables at %a"
                 Position.pp pos)

  and p_nullary_ (self:t) ?(at=false) (s:string) : A.t =
    match Lexer.cur self.lex with
    | COLON ->
      Lexer.junk self.lex;
      let ty = p_expr_ ~ty_expect:(Some A.type_) self 1024 in
      A.var (A.Var.make s (Some ty))
    | _ -> expr_of_string_ ~at self s

  and p_expr_atomic_ ~ty_expect (self:t) : A.t =
    let t = Lexer.cur self.lex in
    let ppos = pos_ self in
    let pos = Lazy.from_val ppos in
    match t with
    | ERROR c ->
      errorf (fun k->k"invalid char '%c' at %a" c Position.pp ppos)
    | LPAREN ->
      Lexer.junk self.lex;
      let e = p_expr_ ~ty_expect self 0 in
      eat_ self ~msg:"atomic expression" RPAREN;
      e
    | LET ->
      Lexer.junk self.lex;
      (* parse `let x = e in e2` *)
      let bs = p_bindings_ self in
      eat_ self ~msg:"let binding body" IN;
      let bod = p_expr_ ~ty_expect self 0 in
      A.let_ ~pos bs bod
    | SYM s ->
      Lexer.junk self.lex;
      begin match fixity_ self s with
        | F_normal -> p_nullary_ self s
        | F_prefix i ->
          let arg = p_expr_ ~ty_expect:None self i in
          let lhs = expr_of_string_ self s in
          A.app ~pos lhs [arg]
        | F_binder i ->
          let vars = p_tyvars_and_dot self [] |> List.rev in
          let body = p_expr_ ~ty_expect self i in
          let c = match K.Ctx.find_const_by_name self.ctx s with
            | None -> assert false
            | Some c -> K.Expr.const self.ctx c
          in
          A.bind ~pos c vars body
        | (F_left_assoc _ | F_right_assoc _ | F_postfix _ | F_infix _) ->
          errorf (fun k->k"unexpected infix operator `%s` at %a"
                     s Position.pp ppos)
      end
    | AT_SYM s -> p_nullary_ ~at:true self s
    | WILDCARD ->
      let ty = A.ty_meta (fresh_ ~pre:"a" ()) in
      A.meta ~pos (fresh_ ~pre:"_" ()) ty
    | QUESTION_MARK_STR s ->
      let ty = A.ty_meta (fresh_ ~pre:"a" ()) in
      A.meta ~pos s ty
    | QUESTION_MARK ->
      begin match self.q_args with
        | [] -> errorf (fun k->k"no interpolation arg at %a" Position.pp ppos)
        | t :: tl -> self.q_args <- tl; A.const ~pos t
      end
    | NUM _ ->
      errorf (fun k->k"TODO: parse numbers") (* TODO *)
    | RPAREN | COLON | DOT | IN | AND | EOF | QUOTED_STR _ ->
      errorf (fun k->k"expected expression at %a" Position.pp ppos)

  (* TODO: parse bound variables as a list of:
      "x : ty" or "x" or "(x y z : ty)" *)

  and p_expr_ ~ty_expect (self:t) (p:precedence) : A.t =
    let lhs = ref (p_expr_atomic_ ~ty_expect self) in
    let p = ref p in
    let continue = ref true in
    while !continue do
      let ppos = Lexer.pos self.lex in
      let pos = Lazy.from_val ppos in
      match Lexer.cur self.lex with
      | EOF -> continue := false
      | LPAREN ->
        Lexer.junk self.lex;
        let e = p_expr_ ~ty_expect:None self 0 in
        eat_ self ~msg:"expression" RPAREN;
        lhs := A.app ~pos !lhs [e]
      | RPAREN | WILDCARD | COLON | DOT | IN
      | LET | AND -> continue := false
      | AT_SYM _ | QUESTION_MARK | QUOTED_STR _ | QUESTION_MARK_STR _ | NUM _ ->
        let e = p_expr_atomic_ ~ty_expect:None self in
        lhs := A.app ~pos !lhs [e];
      | SYM s ->
        Lexer.junk self.lex;
        let f = fixity_ self s in
        begin match f with
          | (F_left_assoc p' | F_right_assoc p' | F_infix p') when p' >= !p ->
            let op = expr_of_string_ self s in
            let rhs = ref (p_expr_atomic_ ~ty_expect:None self) in
            let continue2 = ref true in
            (* parse right-assoc series *)
            while !continue2 do
              match Lexer.cur self.lex with
              | SYM s2 ->
                begin match fixity_ self s2 with
                  | F_right_assoc p2 when p2 = p' ->
                    let ppos = Lexer.pos self.lex in
                    let pos = Lazy.from_val ppos in
                    Lexer.junk self.lex;
                    let e = p_expr_ self ~ty_expect:None p2 in
                    let op2 = expr_of_string_ self s2 in
                    rhs := A.app ~pos op2 [!rhs; e]
                  | _ -> continue2 := false
                end
              | _ -> continue2 := false
            done;
            lhs := A.app ~pos op [!lhs; !rhs];
          | F_normal ->
            let arg = p_nullary_ self s in
            lhs := A.app ~pos !lhs [arg]
          | F_prefix _ | F_postfix _ | F_binder _ ->
            (* TODO: in case of prefix, we could just parse an appliation *)
            errorf (fun k->k"expected infix operator at %a" Position.pp ppos);
          | F_left_assoc _ | F_right_assoc _ | F_infix _ ->
            (* lower precedence *)
            continue := false
        end
      | ERROR c ->
        errorf (fun k->k "unexpected char '%c' at %a" c Position.pp ppos)
    done;
    !lhs

  (* main entry point for expressions *)
  let expr (self:t) : A.t =
    let e = p_expr_ ~ty_expect:None self 0 in
    let last_tok = Lexer.cur self.lex in
    if last_tok <> EOF then (
      errorf (fun k->k"expected end of input after parsing expression, but got %a"
                 Token.pp last_tok);
    );
    e
end

let parse_ast ?q_args ~ctx lex : A.t =
  let p = Parser.create ?q_args ~ctx lex in
  let e =
    try Parser.expr p
    with e ->
      errorf ~src:e (fun k->k"parse error at %a" Position.pp (Lexer.pos lex))
  in
  e

let parse ?q_args ~ctx lex : Expr.t =
  let e = parse_ast ?q_args ~ctx lex in
  A.ty_infer ctx e

(*$inject
  module E = K.Expr
  module Make() = struct
    let ctx = K.Ctx.create ()
    let bool = K.Expr.bool ctx
    let tau = K.Expr.new_ty_const ctx "tau"
    let v s ty = K.Expr.var ctx (K.Var.make s ty)
    let (@->) a b = K.Expr.arrow ctx a b
    let a = K.Expr.new_const ctx "a" tau
    let b = K.Expr.new_const ctx "b" tau
    let c = K.Expr.new_const ctx "c" tau
    let f1 = K.Expr.new_const ctx "f1" (tau @-> tau)
    let g1 = K.Expr.new_const ctx "g1" (tau @-> tau)
    let h1 = K.Expr.new_const ctx "h1" (tau @-> tau)
    let f2 = K.Expr.new_const ctx "f2" (tau @-> tau @-> tau)
    let g2 = K.Expr.new_const ctx "g2" (tau @-> tau @-> tau)
    let h2 = K.Expr.new_const ctx "h2" (tau @-> tau @-> tau)
    let p0 = K.Expr.new_const ctx "p0" bool
    let q0 = K.Expr.new_const ctx "q0" bool
    let r0 = K.Expr.new_const ctx "r0" bool
    let p1 = K.Expr.new_const ctx "p1" (tau @-> bool)
    let q1 = K.Expr.new_const ctx "q1" (tau @-> bool)
    let r1 = K.Expr.new_const ctx "r1" (tau @-> bool)
    let p2 = K.Expr.new_const ctx "p2" (tau @-> tau @-> bool)
    let q2 = K.Expr.new_const ctx "q2" (tau @-> tau @-> bool)
    let r2 = K.Expr.new_const ctx "r2" (tau @-> tau @-> bool)
    let forall = K.Expr.new_const ctx "!" ((tau @-> bool) @-> bool)
    let () = K.Const.set_fixity (K.Expr.as_const_exn forall) (F_binder 10)
    let plus = K.Expr.new_const ctx "+" (tau @-> tau @-> tau)
    let () = K.Const.set_fixity (K.Expr.as_const_exn plus) (F_right_assoc 20)

    let of_str s = Syntax.parse ~ctx (Lexer.create s)
  end

  module M = Make()
  module A = struct
    include A
    let v (s:string) : t = var (A.Var.make s None)
    let vv s : A.var = A.Var.make s None
    let of_str s : A.t = Syntax.parse_ast ~ctx:M.ctx (Lexer.create s)
    let b_forall vars bod : A.t =
      A.bind M.forall (List.map (fun (x,ty)-> A.Var.make x ty) vars) bod
    let c x : t = A.const x
    let (@) a b = A.app a b
  end
  open A
*)

(*$= & ~printer:A.to_string ~cmp:(fun x y->A.to_string x=A.to_string y)
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
  A.(let_ [vv"x", c M.a] (c M.p1 @ [v "x"])) (A.of_str "let x=a in p1 x")
  A.(let_ [vv"x", c M.a; vv"y", c M.b] (c M.p2 @ [v "x"; v"y"])) \
    (A.of_str "let x=a and y=b in p2 x y")
*)

(* TODO: test type inference *)
(*
$= & ~cmp:E.equal ~printer:E.to_string
  M.(f1 @ var "a" tau) (Sy

*)
