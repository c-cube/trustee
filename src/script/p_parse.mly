
%parameter <Ctx : Ast.PARSER_PARAM>

%{
open P_token
open struct
  module A = Ast
  module Loc = Loc
  let mk_loc a b = Loc.of_lex_pos ~ctx:Ctx.ctx a b
end
open A
%}

%type <Ast.top> top
%start top

%%

top: l=statement* EOI { l }

statement:
| FN f=var
    LPAREN vars=vars RPAREN bl=block
  {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ S_fn (f, vars, bl)
  }

block:
| LBRACE l=block_items
  RBRACE
{
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ {bl_items=l}
}

block_items:
| { [] }
| i=block_item_semi bls=block_items { i :: bls }
| i=block_item_atomic SEMI bls=block_items { i :: bls }
| i=block_item_atomic { [ i ] }

%inline block_item_semi:
| LET v=var EQUAL e=expr SEMI
  { S_let (v, e) }
| VAR v=var EQUAL e=expr SEMI
  { S_var (v, e) }
| v=var EQUAL e=expr SEMI
  { S_assign (v, e) }
| WHILE e=expr bl=block
  { S_while (e,bl) }
| BREAK SEMI { S_break }
| CONTINUE SEMI { S_continue }
| RETURN e=expr SEMI
  { S_return e }

%inline block_item_atomic:
| e=expr
  { S_eval e }

expr:
| v=var {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_var v
  }
| f=var LPAREN l=app_args RPAREN {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_app (f, l)
  }

app_args:
| { [] }
| e=expr { [e] }
| e=expr COMMA args=app_args { e :: args }

vars:
|  { [] }
| v=var { [v] }
| v=var COMMA l=vars { v :: l }

var:
| v=IDENT {
  let loc = mk_loc $startpos $endpos in
  (mk ~loc v: A.var)
}

%%
