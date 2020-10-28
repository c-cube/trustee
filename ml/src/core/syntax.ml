
(** {1 Expression parser} *)

open Sigs

module K = Kernel
module Expr = Kernel.Expr
module A = Parse_ast
module AE = Parse_ast.Expr

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
  | EQDEF
  | AT_SYM of string
  | NUM of string
  | END
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
    | EQDEF -> Fmt.string out "EQDEF"
    | WILDCARD -> Fmt.string out "WILDCARD"
    | QUESTION_MARK -> Fmt.string out "QUESTION_MARK"
    | QUESTION_MARK_STR s -> Fmt.fprintf out "QUESTION_MARK_STR %S" s
    | SYM s -> Fmt.fprintf out "SYM %S" s
    | QUOTED_STR s -> Fmt.fprintf out "QUOTED_STR %S" s
    | AT_SYM s -> Fmt.fprintf out "AT_SYM %s" s
    | NUM s -> Fmt.fprintf out "NUM %S" s
    | END -> Fmt.string out "END"
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
          let s = String.sub self.src i0 (j-i0) in
          AT_SYM s
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
          | "end" -> END
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
end

(* We follow a mix of:
   - https://en.wikipedia.org/wiki/Operator-precedence_parser
   - https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
*)
module P_expr = struct
  open P_state
  type precedence = int
  type t = P_state.t

  let create = P_state.create
  let[@inline] pos_ self = Lexer.pos self.lex

  let fixity_ (self:t) (s:string) : K.fixity =
    let module F = Fixity in
    match s with
    | "->" -> F.rassoc 100
    | "pi" -> F.binder 70
    | "with" -> F.binder 1
    | "\\" -> F.binder 50
    | "=" -> F.infix 150
    | _ ->
      match A.Env.find self.env s with
      | None -> F.normal
      | Some (_,f) -> f

  let eat_p ~msg self ~f : token =
    let pos = Lexer.pos self.lex in
    let t2 = Lexer.cur self.lex in
    if f t2 then (
      Lexer.junk self.lex;
      t2
    ) else (
      errorf (fun k->k "unexpected token %a while parsing %s at %a"
                 Token.pp t2 msg Position.pp pos)
    )

  let eat_p' ~msg self ~f : unit =
    ignore (eat_p ~msg self ~f : token)

  let eat_eq ~msg self (t:token) : unit =
    eat_p' ~msg self ~f:(Token.equal t)

  let eat_end ~msg self : unit =
    eat_p' self ~msg ~f:(function END -> true | _ -> false)

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

  let is_ascii = function
    | 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false

  let expr_of_string_ (self:t) ?(at=false) (s:string) : A.expr =
    begin match s with
      | "bool" -> AE.const ~at (A.Env.bool self.env)
      | "=" -> AE.const ~at (A.Env.eq self.env)
      | _ ->
        match Str_tbl.find self.bindings s with
        | u -> AE.var u
        | exception Not_found ->
          let pos = pos_ self in
          begin match A.Env.find self.env s with
            | Some (c,_) -> AE.const ~pos ~at c
            | None ->
              let ty = AE.ty_meta ~pos (fresh_ ()) in
              AE.var ~pos (A.Var.make s (Some ty))
          end
    end

  (* parse let bindings *)
  let rec p_bindings_ self : (A.var * AE.t) list =
    let v = A.Var.make (p_ident self) None in
    eat_p' self ~msg:"`=` in let binding" ~f:(function SYM "=" -> true | _ -> false);
    let e = p_expr_ ~ty_expect:None self 0 in
    if Token.equal (Lexer.cur self.lex) IN then (
      [v, e]
    ) else (
      eat_eq self ~msg:"`and` between let bindings" AND;
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
        let ty = p_expr_ ~ty_expect:(Some AE.type_) self 0 in
        List.rev_map (fun v -> A.Var.make v (Some ty)) names
      | RPAREN | DOT ->
        List.rev_map (fun v -> A.Var.make v None) names
      | _ ->
        errorf (fun k->k"expected group of typed variables at %a" Position.pp ppos)
    in
    loop []

  and p_tyvars_until ~f self acc : token * A.var list =
    let t = Lexer.cur self.lex in
    if f t then (
      Lexer.junk self.lex;
      t, List.rev acc
    ) else (
      match Lexer.cur self.lex with
      | LPAREN ->
        Lexer.junk self.lex;
        let l = p_tyvar_grp_ self in
        eat_eq self ~msg:"group of typed variables" RPAREN;
        p_tyvars_until ~f self (List.rev_append l acc)
      | SYM _ ->
        let l = p_tyvar_grp_ self in
        let last = eat_p ~msg:"bound variables" self ~f in
        last, List.rev @@ List.rev_append l acc
      | _ ->
        let pos = Lexer.pos self.lex in
        errorf (fun k->k "expected list of (typed) variables at %a"
                   Position.pp pos)
    )

  and p_tyvars_and_dot self acc : A.var list =
    let _d, l =
      p_tyvars_until self acc ~f:(function DOT -> true | _ -> false)
    in
    l

  and p_nullary_ (self:t) ?(at=false) (s:string) : AE.t =
    match Lexer.cur self.lex with
    | COLON ->
      Lexer.junk self.lex;
      let ty = p_expr_ ~ty_expect:(Some AE.type_) self 0 in
      AE.var (A.Var.make s (Some ty))
    | _ ->
      let pos = Lexer.pos self.lex in
      match A.Env.find self.env s with
      | Some (c,_) -> AE.const ~pos ~at c
      | None ->
        if s<>"" && (at || is_ascii (String.get s 0)) then (
          expr_of_string_ ~at self s
        ) else (
          errorf (fun k->k"unknown symbol `%s` at %a" s Position.pp pos)
        )

  and p_expr_atomic_ ~ty_expect (self:t) : AE.t =
    let t = Lexer.cur self.lex in
    let pos = pos_ self in
    match t with
    | ERROR c ->
      errorf (fun k->k"invalid char '%c' at %a" c Position.pp pos)
    | LPAREN ->
      Lexer.junk self.lex;
      let e = p_expr_ ~ty_expect self 0 in
      eat_eq self ~msg:"atomic expression" RPAREN;
      e
    | LET ->
      Lexer.junk self.lex;
      (* parse `let x = e in e2` *)
      Log.debugf 5 (fun k->k"parsing let");
      let bs = p_bindings_ self in
      eat_eq self ~msg:"let binding body" IN;
      List.iter (fun (v,_) -> Str_tbl.add self.bindings v.A.v_name v) bs;
      let bod = p_expr_ ~ty_expect self 0 in
      List.iter (fun (v,_) -> Str_tbl.remove self.bindings v.A.v_name) bs;
      AE.let_ ~pos bs bod
    | SYM s ->
      Lexer.junk self.lex;
      begin match fixity_ self s with
        | F_normal -> p_nullary_ self s
        | F_prefix i ->
          let arg = p_expr_ ~ty_expect:None self i in
          let lhs = expr_of_string_ self s in
          AE.app ~pos lhs [arg]
        | F_binder i ->
          let vars = p_tyvars_and_dot self [] in
          let body = p_expr_ ~ty_expect self i in
          begin match s with
            | "\\" -> AE.lambda ~pos vars body
            | "pi" -> AE.ty_pi ~pos vars body
            | "with" -> AE.with_ ~pos vars body
            | _ ->
              match A.Env.find self.env s with
              | None -> assert false
              | Some (c,_) ->
                AE.bind ~at:false ~pos c vars body
          end
        | (F_left_assoc _ | F_right_assoc _ | F_postfix _ | F_infix _) ->
          errorf (fun k->k
                     "unexpected infix operator `%s`@ \
                      while parsing atomic expression@ at %a"
                     s Position.pp pos)
      end
    | AT_SYM s ->
      Lexer.junk self.lex;
      p_nullary_ ~at:true self s
    | WILDCARD ->
      Lexer.junk self.lex;
      AE.wildcard ~pos ()
    | QUESTION_MARK_STR s ->
      Lexer.junk self.lex;
      AE.meta ~pos s None
    | QUESTION_MARK ->
      begin match self.q_args with
        | [] -> errorf (fun k->k"no interpolation arg at %a" Position.pp pos)
        | t :: tl -> self.q_args <- tl; AE.const ~pos (A.Const.of_expr t)
      end
    | NUM _ ->
      errorf (fun k->k"TODO: parse numbers") (* TODO *)
    | RPAREN | COLON | DOT | IN | AND | EOF | QUOTED_STR _ | END | EQDEF ->
      errorf (fun k->k"expected expression at %a" Position.pp pos)

  (* TODO: parse bound variables as a list of:
      "x : ty" or "x" or "(x y z : ty)" *)

  and p_expr_ ~ty_expect (self:t) (p:precedence) : AE.t =
    let lhs = ref (p_expr_atomic_ ~ty_expect self) in
    let p = ref p in
    let continue = ref true in
    while !continue do
      let pos = Lexer.pos self.lex in
      match Lexer.cur self.lex with
      | EOF | END | EQDEF -> continue := false
      | LPAREN ->
        Lexer.junk self.lex;
        let e = p_expr_ ~ty_expect:None self 0 in
        eat_eq self ~msg:"expression" RPAREN;
        lhs := AE.app ~pos !lhs [e]
      | RPAREN | WILDCARD | COLON | DOT | IN
      | LET | AND -> continue := false
      | AT_SYM _ | QUESTION_MARK | QUOTED_STR _ | QUESTION_MARK_STR _ | NUM _ ->
        let e = p_expr_atomic_ ~ty_expect:None self in
        lhs := AE.app ~pos !lhs [e];
      | SYM s ->
        Lexer.junk self.lex;
        let f = fixity_ self s in
        begin match f with
          | (F_left_assoc p' | F_right_assoc p' | F_infix p') when p' >= !p ->
            let rhs = ref (p_expr_atomic_ ~ty_expect:None self) in
            let continue2 = ref true in
            (* parse right-assoc series *)
            while !continue2 do
              match Lexer.cur self.lex with
              | SYM s2 ->
                begin match fixity_ self s2 with
                  | F_right_assoc p2 when p2 = p' ->
                    let pos = Lexer.pos self.lex in
                    Lexer.junk self.lex;
                    let e = p_expr_ self ~ty_expect:None p2 in
                    rhs :=
                      if s2 = "->" then AE.ty_arrow !rhs e
                      else (
                        let op2 = expr_of_string_ self s2 in
                        AE.app ~pos op2 [!rhs; e]
                      )
                  | _ -> continue2 := false
                end
              | _ -> continue2 := false
            done;
            lhs :=
              if s = "->" then AE.ty_arrow ~pos !lhs !rhs
              else if s = "=" then AE.eq ~pos !lhs !rhs
              else (
                let op = expr_of_string_ self s in
                AE.app ~pos op [!lhs; !rhs];
              )
          | F_normal ->
            let arg = p_nullary_ self s in
            lhs := AE.app ~pos !lhs [arg]
          | F_prefix _ | F_postfix _ | F_binder _ ->
            (* TODO: in case of prefix, we could just parse an appliation *)
            errorf (fun k->k"expected infix operator at %a" Position.pp pos);
          | F_left_assoc _ | F_right_assoc _ | F_infix _ ->
            (* lower precedence *)
            continue := false
        end
      | ERROR c ->
        errorf (fun k->k "unexpected char '%c' at %a" c Position.pp pos)
    done;
    !lhs

  let expr_atomic ?ty_expect self : AE.t =
    p_expr_atomic_ ~ty_expect self

  let expr (self:t) : AE.t =
    p_expr_ ~ty_expect:None self 0

  (* main entry point for expressions *)
  let expr_and_eof (self:t) : AE.t =
    let e = expr self in
    let last_tok = Lexer.cur self.lex in
    if last_tok <> EOF then (
      errorf (fun k->k"expected end of input after parsing expression, but got %a"
                 Token.pp last_tok);
    );
    e
end

module P_top = struct
  type t = P_state.t
  open P_state

  (* recover: skip to the next "end" *)
  let try_recover_ self : unit =
    while
      match Lexer.cur self.lex with
      | END -> Lexer.junk self.lex; false
      | _ -> Lexer.junk self.lex; true
    do () done

  let p_def ~pos self : _ =
    let name = P_expr.p_ident self in
    let tok, vars =
      P_expr.p_tyvars_until self []
        ~f:(function COLON | EQDEF -> true |_ -> false)
    in
    Log.debugf 5 (fun k->k"got vars %a" (Fmt.Dump.list A.Var.pp_with_ty) vars);
    let ret = match tok with
      | COLON ->
        Some (P_expr.expr_atomic ~ty_expect:AE.type_ self)
      | _ -> None
    in
    P_expr.eat_p' self
      ~msg:"expect `:=` in a definition after <vars> and optional return type"
      ~f:(function EQDEF -> true | _ -> false);
    Log.debugf 5 (fun k->k"def: return type %a, %d vars, cur tok %a"
                     (Fmt.Dump.option AE.pp) ret (List.length vars)
                     Token.pp (Lexer.cur self.lex));
    let body = P_expr.expr self in
    P_expr.eat_end self ~msg:"expect `end` after a definition";
    A.Top_stmt.def ~pos name vars ret body

  let p_show ~pos self : _ =
    match Lexer.cur self.lex with
    | SYM "expr" ->
      Lexer.junk self.lex;
      let e = P_expr.expr self in
      P_expr.eat_end self ~msg:"expect `end` after `show expr`";
      A.Top_stmt.show_expr ~pos e
    | SYM "proof" ->
      assert false (* TODO: parse proof *)
    | SYM s ->
      Lexer.junk self.lex;
      P_expr.eat_end self ~msg:"expect `end` after `show`";
      A.Top_stmt.show ~pos s
    | _ ->
      errorf (fun k->k{|expected a name, or "expr", or a proof|})

  (* list of toplevel parsers *)
  let parsers = [
    "def", p_def;
    "show", p_show;
  ]

  let top (self:t) : A.top_statement option =
    let parsing = ref None in
    let errm ~pos t out () =
      Fmt.fprintf out
        "expected toplevel statement, but got token %a@ at %a;@ \
         expected one of: [%s]"
        Token.pp t Position.pp pos
        (String.concat "," @@ List.map (fun (s,_) -> String.escaped s) parsers)
    in
    try
      match Lexer.cur self.lex with
      | EOF -> None
      | SYM s as t ->
        let pos = Lexer.pos self.lex in
        begin match List.assoc s parsers with
          | exception Not_found ->
            Log.debugf 5 (fun k->k"unknown toplevek tok %a" Token.pp t);
            let err = errm ~pos t in
            try_recover_ self;
            Some (A.Top_stmt.error ~pos err)
          | p ->
            parsing := Some s;
            Log.debugf 5 (fun k->k"parse toplevel %s" s);
            Lexer.junk self.lex;
            Some (p ~pos self)
        end
      | t ->
        let pos = Lexer.pos self.lex in
        let err = errm ~pos t in
        try_recover_ self;
        Some (A.Top_stmt.error ~pos err)
    with
    | Trustee_error.E e ->
      let pos = Lexer.pos self.lex in
      try_recover_ self;
      let msg out () =
        let parsing out () = match !parsing with
          | None -> ()
          | Some p -> Fmt.fprintf out "@ while parsing `%s`" p
        in
        Fmt.fprintf out
          "expected a toplevel statement%a@ at %a@ @[<2>but got error@ %a@]"
          parsing () Position.pp pos Trustee_error.pp e
      in
      Some (A.Top_stmt.error ~pos msg)
end

let parse_expr ?q_args ~env lex : AE.t =
  let p = P_expr.create ?q_args ~env lex in
  let e =
    try P_expr.expr_and_eof p
    with e ->
      errorf ~src:e (fun k->k"parse error at %a" Position.pp (Lexer.pos lex))
  in
  e

let parse_top ~env lex : A.top_statement option =
  let p = P_state.create ~env lex in
  P_top.top p

let parse_top_l_process ?file ~env lex : _ list =
  let pos = Lexer.pos lex in
  let rec aux acc =
    match parse_top ~env lex with
    | None -> List.rev acc
    | Some st ->
      A.Env.process env st;
      aux (st::acc)
  in
  let l = aux [] in
  let l = match file with
    | None -> l
    | Some f -> A.Top_stmt.enter_file ~pos f :: l
  in
  l

let parse_expr_infer ?q_args ~env lex : Expr.t =
  let e = parse_expr ?q_args ~env lex in
  let ctx = A.Env.ctx env in
  let ty_env = Type_ast.Env.create ctx in
  let e = Type_ast.infer ty_env e in
  Type_ast.generalize ty_env;
  Type_ast.to_expr ctx e

(*$inject
  module E = K.Expr
  module Make() = struct
    let ctx = K.Ctx.create ()
    let env = A.Env.create ctx
    let bool = K.Expr.bool ctx
    let tau = K.Expr.new_ty_const ctx "tau"
    let v s ty = K.Expr.var ctx (K.Var.make s ty)
    let (@->) a b = K.Expr.arrow ctx a b
    let (@@) a b = K.Expr.app ctx a b
    let a = K.Expr.new_const ctx "a0" tau
    let b = K.Expr.new_const ctx "b0" tau
    let c = K.Expr.new_const ctx "c0" tau
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
    let eq = K.Expr.eq ctx
    let () = K.Const.set_fixity (K.Expr.as_const_exn plus) (F_right_assoc 20)

    let of_str s = Syntax.parse_expr_infer ~env (Lexer.create s)
  end

  module M = Make()
  module AE = Parse_ast.Expr
  module A = struct
    include Parse_ast
    include AE
    let v (s:string) : t = var (A.Var.make s None)
    let vv s : A.var = A.Var.make s None
    let of_str s : AE.t = Syntax.parse_expr ~env:M.env (Lexer.create s)
    let b_forall vars bod : AE.t =
      AE.bind (A.Const.of_expr M.forall)
        (List.map (fun (x,ty)-> A.Var.make x ty) vars) bod
    let c x : t = AE.of_expr x
    let (@->) a b = AE.ty_arrow a b
    let (@) a b = AE.app a b
  end
  open A

  let parse_e s : K.Expr.t = Syntax.parse_expr_infer ~env:M.env (Lexer.create s)
*)

(* test printer itself *)
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
  A.(let_ [vv"x", c M.a] (c M.p1 @ [v "x"])) (A.of_str "let x = a0 in p1 x")
  A.(let_ [vv"x", c M.a; vv"y", c M.b] (c M.p2 @ [v "x"; v"y"])) \
    (A.of_str "let x=a0 and y=b0 in p2 x y")
  A.(ty_arrow (v"a")(v"b")) (A.of_str "a->b")
  A.(eq (v"a")(v"b")) (A.of_str "a = b")
  A.(b_forall ["x", Some (c M.a @-> c M.b @-> c M.c)] (A.eq (v"x")(v"x"))) \
    (A.of_str "! (x:a0->b0->c0). x=x")
    A.(lambda [A.Var.make "x" @@ Some (c M.a @-> c M.b @-> c M.c)] \
         (A.eq (v"x")(v"x"))) \
    (A.of_str "\\ (x:a0->b0->c0). x=x")
  A.(of_expr ~at:true M.eq) (A.of_str "@=")
  A.(of_expr M.bool) (A.of_str "bool")
*)

(* test type inference *)
(*$= & ~cmp:E.equal ~printer:E.to_string
  M.(tau @-> tau) (K.Expr.ty_exn M.f1)
  M.(f1 @@ v "a" tau) (parse_e "f1 a")
*)

(* test lexer *)
(*$inject
  module Fmt = CCFormat
  let lex_to_list s =
    let lex = Lexer.create s in
    let rec aux acc =
      match Lexer.next lex with
      | EOF as t -> List.rev (t::acc)
      | t -> aux (t::acc)
    in
    aux []

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
      SYM("world"); \
      RPAREN; \
      EOF; \
    ] \
    (lex_to_list {test| foo + _ bar13(hello! := " co co" end world) |test})
    [ LPAREN; \
      LPAREN; \
      NUM("12"); \
      SYM("+"); \
      END; \
      SYM("f"); \
      LPAREN; \
      SYM("x"); \
      SYM(","); \
      COLON; \
      IN; \
      QUESTION_MARK_STR("a"); \
      QUESTION_MARK; \
      QUESTION_MARK; \
      SYM("b"); \
      SYM("Y"); \
      SYM("\\"); \
      LPAREN; \
      RPAREN; \
      RPAREN; \
      SYM("---"); \
      LET; \
      SYM("z"); \
      RPAREN; \
      SYM("wlet"); \
      RPAREN; \
      EOF; \
    ] \
    (lex_to_list {test|((12+end f(x, : in ?a ? ? b Y \( ))---let z)wlet)|test})
  [EOF] (lex_to_list "  ")
*)
