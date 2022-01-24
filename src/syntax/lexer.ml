
open Common_

module S = Lstream
module LL = Local_loc

type state = Read_next | Done

type st = {
  src: string;
  file: string;
  ctx: LL.ctx;
  mutable i: int;
  mutable start: int;
  mutable st: state;
}

type t = Token.t S.t

let[@inline] loc self : Loc.t =
  let ll = LL.make ~ctx:self.ctx ~off1:self.start ~off2:self.i in
  Loc.make ~ctx:self.ctx ll

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
  ()

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

let next_ (self:st) : Token.t =
  assert (self.st != Done);
  (* skip whitespace *)
  begin
    let in_white = ref true in
    while self.i < String.length self.src && !in_white do
      let c = String.get self.src self.i in
      if c = '/' && self.i+1<String.length self.src &&
         String.get self.src (self.i+1) = '/' then (
        rest_of_line self;
      ) else if c = ' ' || c = '\t' || c = '\n' then (
        self.i <- 1 + self.i;
      ) else (
        in_white := false
      );
    done;
  end;
  self.start <- self.i;
  if self.i >= String.length self.src then (
    self.st <- Done;
    EOF
  ) else (
    let c = String.get self.src self.i in
    match c with
    | '(' -> self.i <- 1 + self.i; LPAREN
    | ')' -> self.i <- 1 + self.i; RPAREN
    | '{' -> self.i <- 1 + self.i; LBRACE
    | '}' -> self.i <- 1 + self.i; RBRACE
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
    | '?' ->
      self.i <- 1 + self.i;
      let i0 = self.i in
      let j =
        read_many
          self (fun c -> is_alpha c || is_digit c || is_symbol c) self.i
      in
      if i0 = j then (
        QUESTION_MARK
      ) else (
        self.i <- j;
        QUESTION_MARK_STR (String.sub self.src i0 (j-i0))
      )
    | '\'' ->
      self.i <- 1 + self.i;
      SINGLE_QUOTE
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
        self.i <- j+1;
        Error.failf ~loc:(loc self) (fun k->k"unterminated '\"' string")
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
    | _ ->
      self.i <- self.i+1;
      ERROR c
  )

let next self () : Token.t * Loc.t * S.is_done =
  if self.st == Done then (
    EOF, loc self, true
  ) else (
    let t = next_ self in
    Log.debugf 20 (fun k->k"TOK.next %a, %a" Token.pp t Loc.pp (loc self));
    t, loc self, self.st == Done
  )

let create ~file src : _ S.t =
  let ctx = LL.create ~filename:file src in
  let self = {
    ctx; src; i=0; file; st=Read_next; start=0;
  } in
  S.create ~next:(next self) ()

(*$= & ~printer:Q.Print.(list Token.to_string)
     [SYM "f"; SYM "x"; EOF] (Lexer.create ~file:"" "f x" |> Lexer.S.to_list)
     [SYM "f"; LPAREN; SYM "x"; SYM"+"; SYM "="; RPAREN; EOF] \
      (Lexer.create ~file:"" "f (x + =)" |> Lexer.S.to_list)
*)

