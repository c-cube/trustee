
module Loc = Loc
module Lex = struct
  include P_lex

  let set_filename lexbuf fname =
    let open Lexing in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = fname}
end
module Token = P_token
module Parse = P_parse
module Ast = Ast
module Error = Error

type 'a or_error = ('a, Error.t) result [@@deriving show]

let parse_top_str_exn ~filename (str:string) : Ast.top =
  let buf = Lexing.from_string ~with_positions:true str in
  Lex.set_filename buf filename;
  let ctx = Loc.create_ctx_string ~filename str in
  let module P = Parse.Make(struct let ctx = ctx end) in
  try
    P.top Lex.token buf
  with P.Error ->
    let loc = Loc.of_lexbuf ~ctx buf in
    Error.fail ~loc "parse error"

let parse_top_str ~filename (str:string) : Ast.top or_error =
  try Ok (parse_top_str_exn ~filename str)
  with
  | Error.E err -> Error err
