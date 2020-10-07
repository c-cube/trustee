
module A = Alcotest

open Trustee_core.Syntax

let t_tok = (module Token : A.TESTABLE with type t = token)
let t_tok_l = Alcotest.list t_tok

let to_list lex =
  let rec aux acc =
    match Lexer.next lex with
    | EOF as t -> List.rev (t::acc)
    | t -> aux (t::acc)
  in
  aux []

let t1 : _ A.test_case = "t1", `Quick, fun () ->
  let lex = Lexer.create {test| foo + _ bar13(hello! " co co" world) |test} in
  A.check t_tok_l "same tokens t1"
    [ SYM("foo");
      SYM("+");
      WILDCARD;
      SYM("bar13");
      LPAREN;
      SYM("hello");
      SYM("!");
      QUOTED_STR(" co co");
      SYM("world");
      RPAREN;
      EOF;
    ]
    (to_list lex)

let t2 = "t2", `Quick, fun () ->
  let lex = Lexer.create
      {test|((12+ f(x, in ?a ? ? b Y \( ))---let z)wlet)|test}
  in
  A.check t_tok_l "same tokens t2"
    [ LPAREN;
      LPAREN;
      NUM("12");
      SYM("+");
      SYM("f");
      LPAREN;
      SYM("x");
      SYM(",");
      IN;
      QUESTION_MARK_STR("a");
      QUESTION_MARK;
      QUESTION_MARK;
      SYM("b");
      SYM("Y");
      SYM("\\");
      LPAREN;
      RPAREN;
      RPAREN;
      SYM("---");
      LET;
      SYM("z");
      RPAREN;
      SYM("wlet");
      RPAREN;
      EOF;
    ]
    (to_list lex)

let t_empty = "t_empty", `Quick, fun () ->
  let lex = Lexer.create "  " in
  A.check t_tok_l "no tokens but EOF" [ EOF; ] (to_list lex)

let suite = "syntax", [t1; t2; t_empty]
