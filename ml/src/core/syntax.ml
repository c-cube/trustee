
(** {1 Expression parser} *)

open Sigs

module K = Kernel
module Expr = Kernel.Expr

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
  | AT_SYM of string
  | NUM of string
  | ERROR of char
  | EOF

type position = {
  line: int;
  col: int;
}

let pp_position out (p:position) : unit =
  Fmt.fprintf out "%d:%d" p.line p.col

module Token = struct
  type t = token
  let pp out = function
    | LPAREN -> Fmt.string out "LPAREN"
    | RPAREN -> Fmt.string out "RPAREN"
    | COLON -> Fmt.string out "COLON"
    | DOT -> Fmt.string out "DOT"
    | LET -> Fmt.string out "LET"
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

  let[@inline] pos self = {line=self.line; col=self.col}

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
        errorf ~src:e (fun k->k "at %a" pp_position (pos self))
    in
    self.cur <- t;
    t

  let[@inline] cur self : token =
    match self.st with
    | Done -> EOF
    | Read_next ->
      let t = next self in
      self.cur <- t;
      t
    | Has_cur -> self.cur
end

module Ast = struct
  type t = {
    loc: position;
    view: view;
    mutable as_e: Expr.t option;
  }

  and var = {
    name: string;
    ty: t;
  }

  and binding = string * t

  and view =
    | Expr of Expr.t
    | Var of var
    | Meta of {
        name: string;
        ty: t;
      }
    | App of t * t list
    | Lambda of var list * t
    | Pi of string list * t
    | With of var list * t
    | Arrow of t list * t
    | Eq of t * t
    | Let of binding list * t

  type st = {
    ctx: K.ctx;
    mutable to_generalize: (string * t) list;
  }

  let nopos = {line=0; col=0}

  let mk_expr ?(loc=nopos) (_self:st) (e:K.expr) : t =
    {loc; view=Expr e; as_e=Some e}

  let mk_var ?(loc=nopos) (_self:st) (v:string) (ty:t) : t =
    {loc; view=Var {name=v; ty}; as_e=None}

  let mk_meta ?(loc=nopos) (self:st) (v:string) (ty:t) : t =
    let m = {loc; view=Meta {name=v; ty}; as_e=None} in
    self.to_generalize <- (v,m) :: self.to_generalize;
    m

  let mk_ty_meta ?(loc=nopos) self name : t =
    let ty = mk_expr ~loc self (Expr.type_ self.ctx) in
    mk_meta ~loc self name ty

  let mk_app ?(loc=nopos) self (f:t) (l:t list) : t =
    assert false (* TODO *)

  (* infer types in [e] *)
  let infer_ (self:st) (e:t) : unit =
    (* TODO
    let rec inf_ty (e:t) : Expr.t =
      match e.as_e with
      | Some e -> e
      | None ->
        begin match e with
          | Expr e -> e.as_e <- Some e; e
          | Var v -> inf_ty v.ty;
          | Meta {name} ->
            assert false (* TODO *)

        end
    in
    aux e
    *)
    ()

  let gen_all_ (self:st) : unit =
    Log.debugf 5
      (fun k->k"gen-all@ on %d variables" (List.length self.to_generalize));
    (* generalize everything *)
    List.iter
      (fun (name,e) ->
         if CCOpt.is_none e.as_e then (
           let v = Expr.var_name self.ctx name (Expr.type_ self.ctx) in
           Log.debugf 10 (fun k->k"generalize %s into %a" name Expr.pp v);
           e.as_e <- Some v;
         ))
      self.to_generalize;
    ()

  (* convert a fully inferred AST expr into an expression *)
  let conv_ (self:st) (e:t) : Expr.t =
    let rec aux e =
      match e.as_e with
      | Some e -> e
      | None ->
        begin match e.view with
          | Expr e -> e
          | Var v -> Expr.var self.ctx (aux_var v)
          | App (f, l) ->
            let f = aux f in
            let l = List.map aux l in
            Expr.app_l self.ctx f l
          | Lambda (vs,bod) ->
            let vs = List.map aux_var vs in
            let bod = aux bod in
            Expr.lambda_l self.ctx vs bod
          | Pi (vs, bod) ->
            let type_ = Expr.type_ self.ctx in
            let vs = List.map (fun s -> K.Var.make s type_) vs in
            let bod = aux bod in
            Expr.pi_l self.ctx vs bod
          | Arrow (args,ret) ->
            Expr.arrow_l self.ctx (List.map aux args) (aux ret)
          | Meta {name} ->
            errorf (fun k->k"meta-variable `%s` should have been generalized" name)
          | Eq (a,b) ->
            Expr.app_eq self.ctx (aux a) (aux b)
          | With (_, t) -> aux t
          | Let (_,t) -> aux t
        end
    and aux_var v =
      let ty = aux v.ty in
      K.Var.make v.name ty
    in
    aux e

  let ty_infer (ctx:K.ctx) (e:t) : Expr.t =
    let st = {ctx; to_generalize=[] } in
    infer_ st e;
    gen_all_ st;
    conv_ st e
end

module Parser = struct
  type t = {
    lex: Lexer.t;
    locals: (string, Ast.var) Hashtbl.t;
    lets: (string, Ast.t) Hashtbl.t;
    mutable q_args: Expr.t list; (* interpolation parameters *)
  }

  let create ?(q_args=[]) (src: Lexer.t) : t =
    { lex=src;
      locals=Hashtbl.create 16;
      lets=Hashtbl.create 16;
      q_args;
    }

  let rec p_expr (self:t) (p:int) : Expr.t =
    assert false

  let expr (self:t) : Expr.t = p_expr self 1024
end

let parse ?q_args ~ctx lex : Expr.t =
  let p = Parser.create ?q_args lex in
  let e =
    try Parser.expr p
    with e ->
      errorf ~src:e (fun k->k"parse error at %a" pp_position (Lexer.pos lex))
  in
  e
