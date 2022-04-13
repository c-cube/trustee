
{
  type token =
    | IDENT of string

    | COLON_STR of string
    | QUOTED_STR of string
    | INT of string

    | VAR
    | LET
    | SEMI
    | FN
    | EQUAL

    | LPAREN
    | RPAREN
    | LBRACKET
    | RBRACKET
    | LBRACE
    | RBRACE

    | PLUS
    | MINUS
    | STAR
    | SLASH
    | LT
    | LEQ
    | GT
    | GEQ

    | EOI

  type unescape_state =
    | Not_escaped
    | Escaped
    | Escaped_int_1 of int
    | Escaped_int_2 of int

  let char_equal (a : char) b = Stdlib.(=) a b

  let error _buf str = failwith str

  let pp_tok out = function
    | IDENT s -> Format.fprintf out "(ident %S)" s
    | QUOTED_STR s -> Format.fprintf out "(quoted_str %S)" s
    | COLON_STR s -> Format.fprintf out "(colon_str %S)" s
    | INT s -> Format.fprintf out "(int %s)" s
    | LPAREN -> Fmt.string out "'('"
    | RPAREN -> Fmt.string out "')'"
    | LBRACKET -> Fmt.string out "'['"
    | RBRACKET -> Fmt.string out "']'"
    | LBRACE -> Fmt.string out "'{'"
    | RBRACE -> Fmt.string out "'}'"
    | PLUS -> Fmt.string out "+"
    | MINUS -> Fmt.string out "-"
    | STAR -> Fmt.string out "*"
    | SLASH -> Fmt.string out "/"
    | LT -> Fmt.string out "'<'"
    | LEQ -> Fmt.string out "'<='"
    | GT -> Fmt.string out "'>'"
    | GEQ -> Fmt.string out "'>='"
    | EOI -> Fmt.string out "eoi"
    | VAR -> Fmt.string out "var"
    | FN -> Fmt.string out "fn"
    | EQUAL -> Fmt.string out "="
    | LET -> Fmt.string out "let"
    | SEMI -> Fmt.string out ";"

  (* remove quotes + unescape *)
  let remove_quotes lexbuf s =
    assert (s.[0] = '"' && s.[String.length s - 1] = '"');
    let buf = Buffer.create (String.length s) in
    let st = ref Not_escaped in
    for i = 1 to String.length s-2 do
      match !st, s.[i] with
      | Escaped, '\\' -> Buffer.add_char buf '\\'; st := Not_escaped
      | Not_escaped, '\\' -> st := Escaped
      | Escaped, 'n' -> Buffer.add_char buf '\n'; st := Not_escaped
      | Escaped, 'r' -> Buffer.add_char buf '\r'; st := Not_escaped
      | Escaped, 't' -> Buffer.add_char buf '\t'; st := Not_escaped
      | Escaped, 'b' -> Buffer.add_char buf '\b'; st := Not_escaped
      | Escaped, '"' -> Buffer.add_char buf '"'; st := Not_escaped
      | Escaped, ('0'..'9' as c) ->
          st := Escaped_int_1 (Char.code c - Char.code '0')
      | Escaped_int_1 i, ('0'..'9' as c) ->
          st := Escaped_int_2 (10*i+Char.code c - Char.code '0')
      | Escaped_int_2 i, ('0'..'9' as c) ->
        let n = 10*i+Char.code c - Char.code '0' in
          if n < 256 then (
            Buffer.add_char buf (Char.chr n);
          ) else (
            (* non-ascii unicode code point: encode to utf8 on the fly *)
            let c =
              try Uchar.of_int n
              with _ ->
                failwith (Printf.sprintf "CCSexp: invalid unicode codepont '%d'" n)
            in
            CCUtf8_string.uchar_to_bytes c (Buffer.add_char buf)
          );
          st := Not_escaped
      | (Escaped | Escaped_int_1 _ | Escaped_int_2 _), c ->
          error lexbuf (Printf.sprintf "wrong escape `%c`" c)
      | Not_escaped, c -> Buffer.add_char buf c;
    done;
    Buffer.contents buf
}

let newline = '\n' | "\r\n"
let white = [' ' '\r' '\t'] | newline

let comment_line = ';' [^ '\n']*
let printable_char = [^ '\n']

let alpha = ['a'-'z' 'A'-'Z']
let num = ['0'-'9']
let alphanum = alpha | num
let id = alpha alphanum*
let string_item =
  ([^ '"' '\\'] | "\\\"" | "\\\\" | "\\b" | "\\n" | "\\t" | "\\r")
let string = '"' string_item* '"'

rule token = parse
  | comment_line { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | white { token lexbuf }
  | eof { EOI }
  | "var" { VAR }
  | "let" { LET }
  | "" { LET }
  | '=' { EQUAL }
  | ';' { SEMI }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { STAR }
  | '/' { SLASH }
  | '<' { LT }
  | "<=" { LEQ }
  | '>' { GT }
  | ">+" { GEQ }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '-'? num+ { INT (Lexing.lexeme lexbuf) }
  | ':' alphanum+ { COLON_STR (Lexing.lexeme lexbuf) }
  | id { ATOM (Lexing.lexeme lexbuf) }
  | string { QUOTED_STR (remove_quotes lexbuf (Lexing.lexeme lexbuf)) }
  | _ as c
    { error lexbuf (Printf.sprintf "lexing failed on char `%c`" c) }

