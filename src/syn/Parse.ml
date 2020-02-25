
module Make(K : Trustee_kernel.S) = struct
  module Trustee = Trustee.Make(K)
  open Trustee
  module T = Expr

  module Ctx = Statement.Ctx

  let parse_statement_exn ctx s =
    let module P = Parser.Make(struct module K = K module Trustee = Trustee let ctx=ctx end) in
    P.parse Lexer.token (Lexing.from_string s)

  let parse_statement ctx s =
    try Ok (parse_statement_exn ctx s)
    with e -> Error (Printexc.to_string e)

  let parse_statement_l_exn ctx s =
    let module P = Parser.Make(struct module K = K module Trustee = Trustee let ctx=ctx end) in
    P.parse_list Lexer.token (Lexing.from_string s)

  let parse_statement_l ctx s =
    try Ok (parse_statement_l_exn ctx s)
    with e -> Error (Printexc.to_string e)
end
