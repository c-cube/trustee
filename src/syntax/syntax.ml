
(** {1 Expression parser} *)

module A = Parse_ast
module AE = Parse_ast.Expr
module TA = Type_ast

type token =
  | LPAREN
  | RPAREN
  | COLON
  | DOT
  | COMMA
  | SEMI_COLON
  | WILDCARD
  | QUESTION_MARK
  | QUESTION_MARK_STR of string
  | SYM of string
  | QUOTE_STR of string (* 'foo *)
  | QUOTED_STR of string
  | LET
  | IN
  | AND
  | EQDEF
  | NUM of string
  | BY
  | END
  | ERROR of char
  | EOF

type location = A.location

module Token = struct
  type t = token
  let pp out = function
    | LPAREN -> Fmt.string out "LPAREN"
    | RPAREN -> Fmt.string out "RPAREN"
    | COLON -> Fmt.string out "COLON"
    | DOT -> Fmt.string out "DOT"
    | COMMA -> Fmt.string out "COMMA"
    | SEMI_COLON -> Fmt.string out "SEMI_COLON"
    | LET -> Fmt.string out "LET"
    | AND -> Fmt.string out "AND"
    | IN -> Fmt.string out "IN"
    | EQDEF -> Fmt.string out "EQDEF"
    | WILDCARD -> Fmt.string out "WILDCARD"
    | QUESTION_MARK -> Fmt.string out "QUESTION_MARK"
    | QUESTION_MARK_STR s -> Fmt.fprintf out "QUESTION_MARK_STR %S" s
    | SYM s -> Fmt.fprintf out "SYM %S" s
    | QUOTE_STR s -> Fmt.fprintf out "QUOTE_STR %S" s
    | QUOTED_STR s -> Fmt.fprintf out "QUOTED_STR %S" s
    | NUM s -> Fmt.fprintf out "NUM %S" s
    | BY -> Fmt.string out "BY"
    | END -> Fmt.string out "END"
    | ERROR c -> Fmt.fprintf out "ERROR '%c'" c
    | EOF -> Fmt.string out "EOF"
  let to_string = Fmt.to_string pp
  let equal : t -> t -> bool = (=)
end

module Lexer : sig
  type t = token Tok_stream.t
  module S = Tok_stream
  val create : file:string -> string -> t
end = struct
  type state = Read_next | Done

  type st = {
    src: string;
    file: string;
    mutable i: int;
    mutable line: int;
    mutable bol: int; (* offset of beginning of line. col=i-bol *)
    mutable start: Position.t;
    mutable st: state;
  }

  module S = Tok_stream
  type t = token Tok_stream.t

  let[@inline] col self : int = self.i - self.bol + 1

  let[@inline] loc self : location =
    let col = col self - 1 in
    {Loc.start=self.start;
     file=self.file;
     end_={Position.line=self.line; col};
    }

  (* skip rest of line *)
  let rest_of_line self : unit =
    assert (self.st != Done);
    while self.i < String.length self.src && String.get self.src self.i != '\n' do
      self.i <- 1 + self.i
    done;
    if self.i < String.length self.src then (
      assert (String.get self.src self.i = '\n');
      self.i <- 1 + self.i;
    );
    self.bol <- self.i;
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

  let next_ (self:st) : token =
    assert (self.st != Done);
    (* skip whitespace *)
    begin
      let in_white = ref true in
      while self.i < String.length self.src && !in_white do
        let c = String.get self.src self.i in
        if c = '#' then (
          rest_of_line self;
        ) else if c = ' ' || c = '\t' then (
          self.i <- 1 + self.i;
        ) else if c = '\n' then (
          self.i <- 1 + self.i;
          self.bol <- self.i;
          self.line <- 1 + self.line;
        ) else (
          in_white := false
        );
      done;
    end;
    let start = {Position.line=self.line; col=col self} in
    self.start <- start;
    if self.i >= String.length self.src then (
      self.st <- Done;
      EOF
    ) else (
      let c = String.get self.src self.i in
      match c with
      | '(' -> self.i <- 1 + self.i; LPAREN
      | ')' -> self.i <- 1 + self.i; RPAREN
      | ',' -> self.i <- 1 + self.i; COMMA
      | ';' -> self.i <- 1 + self.i; SEMI_COLON
      | ':' ->
        self.i <- 1 + self.i;
        if self.i < String.length self.src && String.get self.src self.i = '=' then (
          self.i <- 1 + self.i;
          EQDEF
        ) else (
          COLON
        )
      | '.' -> self.i <- 1 + self.i; DOT
      | '_' -> self.i <- 1 + self.i; WILDCARD
      | ('?' | '\'') as c0 ->
        self.i <- 1 + self.i;
        let i0 = self.i in
        let j =
          read_many
            self (fun c -> is_alpha c || is_digit c || is_symbol c) self.i
        in
        if i0 = j && c0 = '?' then (
          QUESTION_MARK
        ) else if c0 = '?' then (
          self.i <- j;
          QUESTION_MARK_STR (String.sub self.src i0 (j-i0))
        ) else (
          self.i <- j;
          QUOTE_STR (String.sub self.src i0 (j-i0))
        )
      | '"' ->
        self.i <- 1 + self.i;
        let i0 = self.i in
        let j =
          read_many self (fun c -> c <> '"') self.i
        in
        if j < String.length self.src && String.get self.src j = '"' then (
          self.i <- j + 1;
          QUOTED_STR (String.sub self.src i0 (j-i0))
        ) else (
          errorf (fun k->k"unterminated '\"' string")
        )
      | c when is_alpha c ->
        let i0 = self.i in
        let j = read_many
            self (fun c -> is_alpha c || is_digit c || c =='_') self.i in
        self.i <- j;
        let s = String.sub self.src i0 (j-i0) in
        begin match s with
          | "let" -> LET
          | "by" -> BY
          | "and" -> AND
          | "in" -> IN
          | "end" -> END
          | _ -> SYM s
        end
      | c when is_digit c ->
        let i0 = self.i in
        let j = read_many self (fun c -> is_digit c) self.i in
        self.i <- j;
        let s = String.sub self.src i0 (j-i0) in
        NUM s
      | c when is_symbol c ->
        let i0 = self.i in
        self.i <- 1 + self.i;
        let j = read_many self (fun c -> is_symbol c || c=='_') self.i in
        self.i <- j;
        let s = String.sub self.src i0 (j-i0) in
        SYM s
      | _ -> ERROR c
    )

  let next self () : token * location * Tok_stream.is_done =
    if self.st == Done then (
      EOF, loc self, true
    ) else (
      let t =
        try next_ self
        with e ->
          errorf ~src:e (fun k->k "at %a" Loc.pp (loc self))
      in
      (* Log.debugf 20 (fun k->k"TOK.next %a at %a" Token.pp t Loc.pp (loc self)); *)
      t, loc self, self.st == Done
    )

  let create ~file src : _ Tok_stream.t =
    let self = {
      src; i=0; line=1; bol=0; file; st=Read_next; start=Position.none
    } in
    Tok_stream.create ~next:(next self) ()
end

(*$= & ~printer:Q.Print.(list Token.to_string)
     [SYM "f"; SYM "x"; EOF] (Lexer.create ~file:"" "f x" |> Lexer.S.to_list)
     [SYM "f"; LPAREN; SYM "x"; SYM"+"; SYM "="; RPAREN; EOF] \
      (Lexer.create ~file:"" "f (x + =)" |> Lexer.S.to_list)
*)

module P_state = struct
  type t = {
    env: A.Env.t;
    lex: Lexer.t;
    bindings: A.var Str_tbl.t;
    mutable q_args: Expr.t list; (* interpolation parameters *)
  }

  let create ?(q_args=[]) ~env (src: Lexer.t) : t =
    { lex=src;
      env;
      q_args;
      bindings=Str_tbl.create 16;
    }

  let eat_p ~msg self ~f : token * location =
    let t2, loc = Lexer.S.cur self.lex in
    if f t2 then (
      Lexer.S.junk self.lex;
      t2, loc
    ) else (
      errorf (fun k->k "unexpected token %a while parsing;@ %s at %a"
                 Token.pp t2 msg Loc.pp loc)
    )

  let eat_p' ~msg self ~f : unit =
    ignore (eat_p ~msg self ~f : token * _)

  let eat_eq ~msg self (t:token) : unit =
    eat_p' ~msg self ~f:(Token.equal t)

  let eat_end ~msg self : Loc.t =
    let _, loc = eat_p self ~msg ~f:(function END -> true | _ -> false) in
    loc
end

type state = P_state.t

(* We follow a mix of:
   - https://en.wikipedia.org/wiki/Operator-precedence_parser
   - https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
*)
module P_expr : sig
  val expr : ?ty_expect:AE.t -> state -> AE.t
  val expr_atomic : ?ty_expect:AE.t -> state -> AE.t
  val expr_and_eof : state -> AE.t
  val p_tyvars_until : 
    f:(token -> bool) -> state -> A.var list -> token * location * A.var list
  val p_ident : state -> string * location
end = struct
  open P_state
  open Loc.Infix
  type precedence = int
  type t = P_state.t

  let fixity_ (self:t) (s:string) : Fixity.t =
    let module F = Fixity in
    match s with
    | "->" -> F.rassoc 100
    | "with" -> F.binder 1
    | "\\" -> F.binder 50
    | "=" -> F.infix 150
    | _ -> A.Env.fixity self.env s

  (* parse an identifier *)
  let p_ident self : string * location =
    match Lexer.S.cur self.lex with
    | SYM s, loc ->
      Lexer.S.junk self.lex;
      s, loc
    | _, loc ->
      errorf (fun k->k"expected identifier at %a" Loc.pp loc)

  let expr_of_string_ (self:t) ~loc (s:string) : A.expr =
    match Str_tbl.find self.bindings s with
    | u -> AE.var ~loc u
    | exception Not_found -> AE.var ~loc (A.Var.make ~loc s None)

  (* parse let bindings *)
  let rec p_bindings_ self : (A.var * AE.t) list =
    let name, loc = p_ident self in
    let v = A.Var.make ~loc name None in
    Log.debugf 6 (fun k->k"binding: var %a loc=%a" A.Var.pp v Loc.pp v.v_loc);
    eat_eq self EQDEF ~msg:"`:=` in let binding";
    let e = p_expr_ ~ty_expect:None self 0 in
    if Token.equal (fst @@ Lexer.S.cur self.lex) IN then (
      [v, e]
    ) else (
      eat_eq self ~msg:"`and` between let bindings" AND;
      let vs = p_bindings_ self in
      (v,e) :: vs
    )

  and p_tyvar_grp_ self : A.var list =
    let rec loop names =
      match Lexer.S.cur self.lex with
      | SYM s, loc ->
        Lexer.S.junk self.lex;
        loop ((s,loc)::names)
      | COLON, _loc ->
        Lexer.S.junk self.lex;
        let ty = p_expr_ ~ty_expect:(Some AE.type_) self 0 in
        List.rev_map (fun (v,loc) -> A.Var.make ~loc v (Some ty)) names
      | (RPAREN | DOT), _loc ->
        List.rev_map (fun (v,loc) -> A.Var.make ~loc v None) names
      | _, loc ->
        errorf (fun k->k"expected group of typed variables at %a" Loc.pp loc)
    in
    loop []

  and p_tyvars_until ~f self acc : token * location * A.var list =
    let t, loc = Lexer.S.cur self.lex in
    if f t then (
      Lexer.S.junk self.lex;
      t, loc, List.rev acc
    ) else (
      match Lexer.S.cur self.lex with
      | LPAREN, _loc ->
        Lexer.S.junk self.lex;
        let l = p_tyvar_grp_ self in
        eat_eq self ~msg:"group of typed variables" RPAREN;
        p_tyvars_until ~f self (List.rev_append l acc)
      | SYM _, loc ->
        let l = p_tyvar_grp_ self in
        let last, _ = eat_p self ~f ~msg:"`.` terminating list of bound variables" in
        last, loc, List.rev @@ List.rev_append l acc
      | _, loc ->
        errorf (fun k->k "expected list of (typed) variables at %a"
                   Loc.pp loc)
    )

  and p_tyvars_and_dot self acc : A.var list =
    let _d, _loc, l =
      p_tyvars_until self acc ~f:(function DOT -> true | _ -> false)
    in
    l

  and p_nullary_ ~loc (self:t) (s:string) : AE.t =
    Log.debugf 6 (fun k->k"nullary `%s` loc=%a" s Loc.pp loc);
    match Lexer.S.cur self.lex with
    | COLON, _ ->
      Lexer.S.junk self.lex;
      let ty = p_expr_ ~ty_expect:(Some AE.type_) self 0 in
      let loc = AE.loc ty ++ loc in
      AE.var ~loc (A.Var.make ~loc s (Some ty))
    | _ ->
      if s<>"" then (
        expr_of_string_ ~loc self s
      ) else (
        errorf (fun k->k"unknown symbol `%s` at %a" s Loc.pp loc)
      )

  and p_expr_atomic_ ~ty_expect (self:t) : AE.t =
    let t, loc_t = Lexer.S.cur self.lex in
    match t with
    | ERROR c ->
      errorf (fun k->k"invalid char '%c' at %a" c Loc.pp loc_t)
    | LPAREN ->
      Lexer.S.junk self.lex;
      let e = p_expr_ ~ty_expect self 0 in
      eat_eq self ~msg:"atomic expression" RPAREN;
      e
    | LET ->
      Lexer.S.junk self.lex;
      (* parse `let x = e in e2` *)
      Log.debugf 5 (fun k->k"parsing let");
      let bs = p_bindings_ self in
      eat_eq self ~msg:"let binding body" IN;
      List.iter (fun (v,_) -> Str_tbl.add self.bindings v.A.v_name v) bs;
      let bod = p_expr_ ~ty_expect self 0 in
      List.iter (fun (v,_) -> Str_tbl.remove self.bindings v.A.v_name) bs;
      AE.let_ ~loc:(loc_t ++ AE.loc bod) bs bod
    | SYM s ->
      Lexer.S.junk self.lex;
      begin match fixity_ self s with
        | _ when fst (Lexer.S.cur self.lex) = RPAREN ->
          (* case: `(=)` or `(+)`: return the sybol *)
          p_nullary_ ~loc:loc_t self s
        | F_normal -> p_nullary_ ~loc:loc_t self s
        | F_prefix i ->
          let arg = p_expr_ ~ty_expect:None self i in
          let lhs = expr_of_string_ ~loc:loc_t self s in
          AE.app lhs arg
        | F_binder i ->
          let vars = p_tyvars_and_dot self [] in
          let body = p_expr_ ~ty_expect self i in
          let loc = loc_t ++ AE.loc body in
          begin match s with
            | "\\" -> AE.lambda ~loc vars body
            | "with" -> AE.with_ ~loc vars body
            | _ ->
              let b = AE.var ~loc:loc_t (A.Var.make ~loc:loc_t s None) in
              AE.bind ~b_loc:loc_t ~loc b vars body
          end
        | (F_left_assoc _ | F_right_assoc _ | F_postfix _ | F_infix _) ->
          errorf (fun k->k
                     "unexpected infix operator `%s`@ \
                      while parsing atomic expression@ at %a"
                     s Loc.pp loc_t)
      end
    | WILDCARD ->
      Lexer.S.junk self.lex;
      AE.wildcard ~loc:loc_t ()
    | QUESTION_MARK_STR s ->
      Lexer.S.junk self.lex;
      AE.meta ~loc:loc_t s None
    | QUOTE_STR s ->
      Lexer.S.junk self.lex;
      AE.ty_var ~loc:loc_t s
    | QUESTION_MARK ->
      begin match self.q_args with
        | [] -> errorf (fun k->k"no interpolation arg at %a" Loc.pp loc_t)
        | t :: tl -> self.q_args <- tl; AE.of_k_expr ~loc:loc_t t
      end
    | NUM _ ->
      errorf (fun k->k"TODO: parse numbers") (* TODO *)
    | RPAREN | COLON | DOT | IN | AND | EOF | QUOTED_STR _
    | BY | END | EQDEF | SEMI_COLON | COMMA ->
      errorf (fun k->k"expected expression at %a" Loc.pp loc_t)

  and p_expr_app_ ~ty_expect self : AE.t =
    let e = ref (p_expr_atomic_ ~ty_expect self) in
    let continue = ref true in
    while !continue do
      match Lexer.S.cur self.lex with
      | LPAREN, _ ->
        Lexer.S.junk self.lex;
        let e2 = p_expr_ self ~ty_expect:None 0 in
        eat_eq self RPAREN ~msg:"expect `)` to close sub-expression";
        e := AE.app !e e2;
      | SYM s, loc_s when fixity_ self s = Fixity.F_normal ->
        Lexer.S.junk self.lex;
        let e2 = p_nullary_ ~loc:loc_s self s in
        e := AE.app !e e2;
      | _ -> continue := false;
    done;
    !e

  and p_expr_ ~ty_expect (self:t) (p:precedence) : AE.t =
    let lhs = ref (p_expr_app_ ~ty_expect self) in
    Log.debugf 6 (fun k->k"lhs: `%a` loc=%a prec=%d" AE.pp !lhs Loc.pp (AE.loc !lhs) p);
    let p = ref p in
    let continue = ref true in
    while !continue do
      match Lexer.S.cur self.lex with
      | (EOF | END | BY | EQDEF), _ -> continue := false
      | LPAREN, _ ->
        Lexer.S.junk self.lex;
        let e = p_expr_ ~ty_expect:None self 0 in
        eat_eq self ~msg:"expression" RPAREN;
        lhs := AE.app !lhs e
      | (RPAREN | WILDCARD | COLON | DOT | IN | COMMA | SEMI_COLON
      | LET | AND), _loc -> continue := false
      | (QUESTION_MARK | QUOTED_STR _ | QUOTE_STR _
        | QUESTION_MARK_STR _ | NUM _), _ ->
        let e = p_expr_atomic_ ~ty_expect:None self in
        lhs := AE.app !lhs e;
      | SYM s, loc_s ->
        Lexer.S.junk self.lex;
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
                    Lexer.S.junk self.lex;
                    let e = p_expr_ self ~ty_expect:None p2 in
                    rhs := (
                      if s2 = "->" then (
                        let loc = loc_s2 ++ AE.loc e in
                        AE.ty_arrow ~loc !rhs e
                      ) else (
                        let op2 = expr_of_string_ ~loc:loc_s2 self s2 in
                        AE.app_l op2 [!rhs; e]
                      )
                    )
                  | _ -> continue2 := false
                end
              | _ -> continue2 := false
            done;
            lhs := (
              let loc = loc_s ++ AE.loc !lhs ++ AE.loc !rhs in
              Log.debugf 6 (fun k->k"loc lhs: %a" Loc.pp (AE.loc !lhs));
              if s = "->" then AE.ty_arrow ~loc !lhs !rhs
              else if s = "=" then AE.eq ~loc !lhs !rhs
              else (
                let op = expr_of_string_ ~loc:loc_s self s in
                AE.app_l op [!lhs; !rhs]
              )
            )
          | F_normal ->
            let arg = p_nullary_ ~loc:loc_s self s in
            lhs := AE.app !lhs arg
          | F_prefix _ | F_postfix _ | F_binder _ ->
            (* TODO: in case of prefix, we could just parse an appliation *)
            errorf (fun k->k"expected infix operator at %a" Loc.pp loc_s);
          | F_left_assoc _ | F_right_assoc _ | F_infix _ ->
            (* lower precedence *)
            continue := false
        end
      | ERROR c, loc ->
        errorf (fun k->k "unexpected char '%c' at %a" c Loc.pp loc)
    done;
    !lhs

  let expr_atomic ?ty_expect self : AE.t =
    p_expr_atomic_ ~ty_expect self

  let expr ?ty_expect (self:t) : AE.t =
    p_expr_ ~ty_expect self 0

  (* main entry point for expressions *)
  let expr_and_eof (self:t) : AE.t =
    let e = expr self in
    let last_tok, _l = Lexer.S.cur self.lex in
    if last_tok <> EOF then (
      errorf (fun k->k"expected end of input after parsing expression, but got %a"
                 Token.pp last_tok);
    );
    e
end

module P_subst : sig
  val subst : state -> A.subst
end = struct
  open P_state
  open Loc.Infix

  let subst st =
    let _, loc1 = Lexer.S.cur st.lex in
    let rec p_binding ~expect_comma s =
      let tok, loc_t = Lexer.S.cur st.lex in
      match tok with
      | END ->
        Lexer.S.junk st.lex;
        A.Subst.mk_ ~loc:(loc1 ++ loc_t) (List.rev s)
      | COMMA when expect_comma ->
        Lexer.S.junk st.lex;
        p_binding ~expect_comma:false s
      | _ ->
        if expect_comma then (
          errorf
            (fun k->k"expected `,` or `end` after a substitution binding")
        ) else (
          let v, loc_v = P_expr.p_ident st in
          eat_eq st ~msg:"expect `:=` in substitution" EQDEF;
          let e = P_expr.expr st in
          let s = ({A.view=v;loc=loc_v},e)::s in
          p_binding ~expect_comma:true s
        )
    in
    eat_eq ~msg:"expect `subst`" st (SYM "subst");
    p_binding ~expect_comma:false []
end

module P_proof : sig
  type t = P_state.t
  val proof : t -> A.Proof.t
end = struct
  module Rule = Proof.Rule
  type t = P_state.t
  open P_state
  open Loc.Infix

  (* TODO: error recovery (until "in" or "end") for steps *)
  let rec p_step self : A.Proof.step =
    let p_start_r ~loc (r:string A.with_loc) =
      let loc = ref loc in
      match A.Env.find_rule self.env r.view with
      | None ->
        errorf
          (fun k->k"unknown rule '%s'@ while parsing a proof step@ at %a"
              r.view Loc.pp r.loc)
      | Some sgn ->
        Log.debugf 5 (fun k->k"rule `%s` has signature %a" r.view
                         Rule.pp_signature sgn);
        let args =
          List.map
            (function
              | Rule.Arg_expr ->
                let e = P_expr.expr_atomic self in
                loc := !loc ++ AE.loc e;
                A.Proof.arg_expr e
              | Rule.Arg_subst ->
                let s = P_subst.subst self in
                A.Proof.arg_subst s
              | Rule.Arg_thm ->
                begin match Lexer.S.cur self.lex with
                  | LPAREN, _ ->
                    Lexer.S.junk self.lex;
                    let s = p_step self in
                    loc := !loc ++ A.Proof.s_loc s;
                    eat_eq self RPAREN ~msg:"expect `)` after a proof sub-step";
                    A.Proof.arg_step s
                  | SYM s, loc_s ->
                    loc := !loc ++ loc_s;
                    Lexer.S.junk self.lex;
                    A.Proof.arg_var {A.view=s; loc=loc_s}
                  | tok, loc_t ->
                    errorf
                      (fun k->k"expected a theorem or sub-step@ but got %a@ at %a"
                          Token.pp tok Loc.pp loc_t)
                end)
            sgn
        in
        A.Proof.step_apply_rule ~loc:!loc r args
    in
    let tok, loc = Lexer.S.cur self.lex in
    try
      begin match tok, loc with
        | SYM "proof", loc_p ->
          (* subproof *)
          let p = proof self in
          A.Proof.step_subproof ~loc:(loc_p ++ A.Proof.loc p) p
        | LPAREN, _ ->
          Lexer.S.junk self.lex;
          let r, r_loc = P_expr.p_ident self in
          let s = p_start_r ~loc:r_loc {loc=r_loc; view=r} in
          eat_eq self RPAREN ~msg:"expect `)` to close the step";
          s
        | SYM r, r_loc ->
          Lexer.S.junk self.lex;
          p_start_r ~loc:r_loc {loc=r_loc; view=r}
        | _, loc ->
          errorf (fun k->k"expected to parse a proof step@ at %a" Loc.pp loc)
      end
    with Trustee_error.E e ->
      A.Proof.step_error ~loc (fun out () -> Trustee_error.pp out e)

  and p_lets self acc : _ list =
    match Lexer.S.cur self.lex with
    | LET, _ ->
      Lexer.S.junk self.lex;
      let let_ =
        match Lexer.S.cur self.lex with
        | SYM "expr", _ ->
          Lexer.S.junk self.lex;
          let name, loc_name = P_expr.p_ident self in
          eat_eq self EQDEF ~msg:"expect `:=` after the name of the step";
          let e = P_expr.expr self in
          A.Proof.let_expr {loc=loc_name;view=name} e
        | _ ->
          let name, loc_name = P_expr.p_ident self in
          eat_eq self EQDEF ~msg:"expect `:=` after the name of the step";
          let s = p_step self in
          A.Proof.let_step {view=name;loc=loc_name} s
      in
      Log.debugf 5 (fun k->k"parsed pr-let %a" A.Proof.pp_pr_let let_);
      eat_eq self IN ~msg:"expect `in` after a `let`-defined proof step";
      p_lets self (let_ :: acc)
    | _ -> List.rev acc

  and proof (self:t) : A.Proof.t =
    Log.debugf 5 (fun k->k"start parsing proof");
    let _, loc =
      eat_p self ~msg:"expect `proof` to start a proof"
        ~f:(function SYM "proof" -> true | _ -> false)
    in
    let lets = p_lets self [] in
    let last = p_step self in
    let loc_end = eat_end self ~msg:"proof must finish with `end`" in
    let p = A.Proof.make ~loc:(loc ++ loc_end) lets last in
    p
end

module P_top = struct
  open P_state
  open Loc.Infix

  (* recover: skip to the next "end" *)
  let try_recover_end_ (self:t) : location =
    let loc = ref (snd @@ Lexer.S.cur self.lex) in
    while
      let tok, tok_loc = Lexer.S.cur self.lex in
      loc := Loc.(tok_loc ++ !loc);
      match tok with
      | END | EOF -> Lexer.S.junk self.lex; false
      | _ -> Lexer.S.junk self.lex; true
    do () done;
    !loc

  let p_def ~loc:loc0 self : A.top_statement =
    let name, loc_name = P_expr.p_ident self in
    let tok, _tok_loc, vars =
      P_expr.p_tyvars_until self []
        ~f:(function COLON | EQDEF | BY -> true |_ -> false)
    in
    Log.debugf 5 (fun k->k"got vars %a" (Fmt.Dump.list A.Var.pp_with_ty) vars);
    let tok, ret = match tok with
      | COLON ->
        let e =  P_expr.expr ~ty_expect:AE.type_ self in
        let tok, _ = Lexer.S.cur self.lex in
        Lexer.S.junk self.lex;
        tok, Some (e)
      | _ -> tok, None
    in
    let th_name = match tok with
      | BY ->
        let view, loc = P_expr.p_ident self in
        Some {A.view;loc}
      | _ -> None
    in
    eat_p' self
      ~msg:"expect `:=` in a definition after <vars> and optional return type"
      ~f:(function EQDEF -> true | _ -> false);
    Log.debugf 5 (fun k->k"def: return type %a, %d vars, curren token: %a"
                     (Fmt.Dump.option AE.pp_quoted) ret (List.length vars)
                     Token.pp (fst @@ Lexer.S.cur self.lex));
    let body = P_expr.expr self in
    let loc = loc0 ++ eat_end self ~msg:"expect `end` after a definition" in
    A.Top_stmt.def ~loc {view=name;loc=loc_name} ~th_name vars ret body

  let p_declare ~loc self : A.top_statement =
    let name, loc_name = P_expr.p_ident self in
    eat_eq self COLON ~msg:"expect `:` in a type declaration";
    let ty = P_expr.expr_atomic ~ty_expect:AE.type_ self in
    Log.debugf 5 (fun k->k"decl: type %a" AE.pp ty);
    let loc = loc ++ eat_end self ~msg:"expect `end` after a declaration" in
    A.Top_stmt.decl ~loc {A.view=name;loc=loc_name} ty

  let p_show ~loc self : _ =
    match Lexer.S.cur self.lex with
    | SYM "expr", _ ->
      Lexer.S.junk self.lex;
      let e = P_expr.expr self in
      let loc = loc ++ eat_end self ~msg:"expect `end` after `show expr`" in
      A.Top_stmt.show_expr ~loc e
    | SYM "proof", _ ->
      let p = P_proof.proof self in
      let loc = loc ++ eat_end self ~msg:"expect `end` after `show proof`" in
      A.Top_stmt.show_proof ~loc p
    | SYM s, s_loc ->
      Lexer.S.junk self.lex;
      let loc = loc ++ eat_end self ~msg:"expect `end` after `show`" in
      A.Top_stmt.show ~loc {view=s;loc=s_loc}
    | _ ->
      errorf (fun k->k{|expected a name, or "expr", or a proof|})

  let p_thm ~loc self : _ =
    let name, loc_name = P_expr.p_ident self in
    eat_eq self EQDEF ~msg:"expect `:=` after the theorem's name";
    let e = P_expr.expr self
        ~ty_expect:(A.Env.bool self.env)
    in
    eat_eq self BY ~msg:"expect `by` after the theorem's statement";
    let pr = P_proof.proof self in
    let loc = loc ++ eat_end self ~msg:"expect `end` after the theorem" in
    A.Top_stmt.theorem ~loc {A.view=name;loc=loc_name} (A.Goal.make_nohyps e) pr

  let p_goal ~loc self : _ =
    let e =
      P_expr.expr self ~ty_expect:(A.Env.bool self.env)
    in
    eat_eq self BY ~msg:"expect `by` after the goal's statement";
    let pr = P_proof.proof self in
    let loc = loc ++ eat_end self ~msg:"expect `end` after the goal" in
    A.Top_stmt.goal ~loc (A.Goal.make_nohyps e) pr

  let p_fixity ~loc self =
    let name, loc_name = P_expr.p_ident self in
    eat_eq self EQDEF ~msg:"expect `:=` after symbol";
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
        errorf
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
    let loc = loc ++ eat_end self ~msg:"expect `end` after fixity declarations" in
    A.Top_stmt.fixity ~loc {A.view=name;loc=loc_name} fix

  (* list of toplevel parsers *)
  let parsers = [
    "def", p_def;
    "show", p_show;
    "fixity", p_fixity;
    "declare", p_declare;
    "theorem", p_thm;
    "goal", p_goal;
  ]

  let top (self:t) : A.top_statement option =
    let parsing = ref None in
    let errm ~loc t out () =
      Fmt.fprintf out
        "expected toplevel statement, but got token %a@ at %a;@ \
         expected one of: [%s]"
        Token.pp t Loc.pp loc
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
            let loc = loc ++ try_recover_end_ self in
            Some (A.Top_stmt.error ~loc err)
          | p ->
            parsing := Some s;
            Log.debugf 5 (fun k->k"parse toplevel %s" s);
            Lexer.S.junk self.lex;
            Some (p ~loc self)
        end
      | t, loc ->
        let err = errm ~loc t in
        let loc = loc ++ try_recover_end_ self in
        Some (A.Top_stmt.error ~loc err)
    with
    | Trustee_error.E e ->
      let _, loc = Lexer.S.cur self.lex in
      let loc = loc ++ try_recover_end_ self in
      let msg out () =
        let parsing out () = match !parsing with
          | None -> ()
          | Some p -> Fmt.fprintf out "@ while parsing `%s`" p
        in
        Fmt.fprintf out
          "expected a toplevel statement%a@ at %a@ @[<2>but got error@ %a@]"
          parsing () Loc.pp loc Trustee_error.pp e
      in
      Some (A.Top_stmt.error ~loc msg)
end

let parse_expr ?q_args ~env lex : AE.t =
  let p = P_state.create ?q_args ~env lex in
  let e =
    try P_expr.expr_and_eof p
    with e ->
      errorf ~src:e (fun k->k"parse error at %a" Loc.pp (snd @@ Lexer.S.cur lex))
  in
  e

let parse_top ~env lex : A.top_statement option =
  let p = P_state.create ~env lex in
  P_top.top p

let parse_top_l_process ?file ~env lex : _ list =
  let _, loc = Lexer.S.cur lex in
  let rec aux acc =
    match parse_top ~env lex with
    | None -> List.rev acc
    | Some st ->
      (* FIXME: not needed anymore:
         A.Env.process env st; *)
      aux (st::acc)
  in
  let l = aux [] in
  let l = match file with
    | None -> l
    | Some f -> A.Top_stmt.enter_file ~loc f :: l
  in
  l

