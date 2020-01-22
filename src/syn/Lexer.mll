
{
  open Tokens
}
let printable_char = [^ '\n']
let comment_line = '#' printable_char*

let sym = [^ '"' '(' ')' '\\' ' ' '.' '\t' '\r' '\n']
let atom = ['a' - 'z' 'A'-'Z' '0'-'9'] sym*

rule token = parse
  | eof { EOI }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | comment_line { token lexbuf }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | '\\' { LAMBDA }
  | "pi" { PI }
  | "/\\" { AND }
  | "\\/" { OR }
  | "|-" { VDASH }
  | "," { COMMA }
  | "->" { ARROW }
  | "=" { EQ }
  | "~" { NOT }
  | "." { DOT }
  | ":" { COLON }
  | "decl" { ST_DECL }
  | "prove" { ST_PROVE }
  | atom { IDENT(Lexing.lexeme lexbuf) }
  | _ as c
    {
      failwith @@ Printf.sprintf "unexpected char '%c'" c
    }

{

}
