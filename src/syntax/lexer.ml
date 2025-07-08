open Common_
module S = Lstream
module LL = Local_loc

type state =
  | Read_next
  | Done

type st = {
  src: string;
  file: string;
  ctx: LL.ctx;
  loc_offset: int;
  mutable i: int;
  mutable start: int;
  mutable st: state;
}

type t = Token.t S.t

let[@inline] loc self : Loc.t =
  let off1 = self.start + self.loc_offset in
  let off2 = self.i + self.loc_offset in
  let ll = LL.make ~ctx:self.ctx ~off1 ~off2 in
  Loc.make ~ctx:self.ctx ll

let[@inline] is_idx (self : st) (i : int) = i < String.length self.src
let[@inline] get (self : st) (i : int) : char = String.get self.src i

(* skip rest of line *)
let rest_of_line self : unit =
  assert (self.st != Done);
  while is_idx self self.i && get self self.i != '\n' do
    self.i <- 1 + self.i
  done;
  if is_idx self self.i then (
    assert (get self self.i = '\n');
    self.i <- 1 + self.i
  );
  ()

let is_alpha = function
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

let is_symbol = function
  | '=' | ',' | ';' | '<' | '>' | '!' | '/' | '\\' | '+' | '-' | '|' | '^' | '~'
  | '*' | '&' | '%' | '@' ->
    true
  | _ -> false

let rec read_many self f j : int =
  if is_idx self j then (
    let c = get self j in
    if f c then
      read_many self f (j + 1)
    else
      j
  ) else
    j

let next_ (self : st) : Token.t =
  assert (self.st != Done);
  (* skip whitespace *)
  (let in_white = ref true in
   while is_idx self self.i && !in_white do
     let c = get self self.i in
     if c = '/' && is_idx self (self.i + 1) && get self (self.i + 1) = '/' then
       rest_of_line self
     else if c = ' ' || c = '\t' || c = '\n' then
       self.i <- 1 + self.i
     else
       in_white := false
   done);
  self.start <- self.i;
  if self.i >= String.length self.src then (
    self.st <- Done;
    EOF
  ) else (
    let c = get self self.i in
    match c with
    | '(' ->
      self.i <- 1 + self.i;
      LPAREN
    | ')' ->
      self.i <- 1 + self.i;
      RPAREN
    | ',' ->
      self.i <- 1 + self.i;
      COMMA
    | ':' ->
      self.i <- 1 + self.i;
      if is_idx self self.i && get self self.i = '=' then (
        self.i <- 1 + self.i;
        EQDEF
      ) else
        COLON
    | '.' ->
      self.i <- 1 + self.i;
      DOT
    | '_' ->
      self.i <- 1 + self.i;
      WILDCARD
    | '?' ->
      self.i <- 1 + self.i;
      let i0 = self.i in
      let j =
        read_many self (fun c -> is_alpha c || is_digit c || is_symbol c) self.i
      in
      if i0 = j then
        QUESTION_MARK
      else (
        self.i <- j;
        QUESTION_MARK_STR (String.sub self.src i0 (j - i0))
      )
    | '"' ->
      self.i <- 1 + self.i;
      let i0 = self.i in
      let j = read_many self (fun c -> c <> '"') self.i in
      if is_idx self j && get self j = '"' then (
        self.i <- j + 1;
        QUOTED_STR (String.sub self.src i0 (j - i0))
      ) else (
        self.i <- j + 1;
        Error.failf ~loc:(loc self) (fun k -> k "unterminated '\"' string")
      )
    | c when is_alpha c ->
      let i0 = self.i in
      let j =
        read_many self (fun c -> is_alpha c || is_digit c || c == '_') self.i
      in
      self.i <- j;
      let s = String.sub self.src i0 (j - i0) in
      (match s with
      | "let" -> LET
      | "in" -> IN
      | _ -> SYM s)
    | c when is_digit c ->
      let i0 = self.i in
      let j = read_many self (fun c -> is_digit c) self.i in
      self.i <- j;
      let s = String.sub self.src i0 (j - i0) in
      NUM s
    | c when is_symbol c ->
      let i0 = self.i in
      self.i <- 1 + self.i;
      let j = read_many self (fun c -> is_symbol c || c == '_') self.i in
      self.i <- j;
      let s = String.sub self.src i0 (j - i0) in
      SYM s
    | _ ->
      self.i <- self.i + 1;
      ERROR c
  )

let next self () : Token.t * Loc.t * S.is_done =
  if self.st == Done then
    EOF, loc self, true
  else (
    let t = next_ self in
    Log.debugf 20 (fun k ->
        k "TOK.next %a, %a" Token.pp t Loc.pp_compact (loc self));
    t, loc self, self.st == Done
  )

let create ?(loc_offset = 0) ?src_string ~file src : _ S.t =
  let ctx =
    let ctx_src =
      match src_string with
      | Some s -> s
      | None -> src
    in
    LL.create ~filename:file ctx_src
  in
  let self = { ctx; loc_offset; src; i = 0; file; st = Read_next; start = 0 } in
  S.create ~next:(next self) ()

(*$= & ~printer:Q.Print.(list Token.to_string)
     [SYM "f"; SYM "x"; EOF] (Lexer.create ~file:"" "f x" |> Lexer.S.to_list)
     [SYM "f"; LPAREN; SYM "x"; SYM"+"; SYM "="; RPAREN; EOF] \
      (Lexer.create ~file:"" "f (x + =)" |> Lexer.S.to_list)
*)
