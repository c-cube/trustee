
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
| LET v=var EQUAL e=expr SEMI bls=block_items
  { S_let (v, e) :: bls }
| e=expr
  { [S_eval e] }
| e=expr SEMI bls=block_items
  { S_eval e :: bls }

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
