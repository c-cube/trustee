
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
%type <Ast.statement> statement
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
| e=expr SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ S_eval e
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
  { Bl_let (v, e) }
| VAR v=var EQUAL e=expr SEMI
  { Bl_var (v, e) }
| v=var EQUAL e=expr SEMI
  { Bl_assign (v, e) }
| WHILE e=expr bl=block
  { Bl_while (e,bl) }
| BREAK SEMI { Bl_break }
| CONTINUE SEMI { Bl_continue }
| RETURN e=expr SEMI
  { Bl_return e }

%inline block_item_atomic:
| e=expr
  { Bl_eval e }

expr:
| e=or_expr { e }
| f=var LPAREN l=app_args RPAREN {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_app (f, l)
  }

or_expr:
| e=and_expr { e }
| a=or_expr OR b=and_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (Or, a, b)
  }

and_expr:
| e=bool_expr { e }
| a=and_expr AND b=bool_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (And, a, b)
  }

bool_expr:
| e=not_expr { e }
| a=not_expr op=bool_op b=not_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (op, a, b)
  }

%inline bool_op:
| LT { Lt }
| LEQ { Leq }
| GT { Gt }
| GEQ { Geq }
| EQ { Eq }
| NEQ { Neq }

not_expr:
| e=add_expr { e }
| NOT e=add_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_unop (Not, e)
  }

add_expr:
| e=mult_expr { e }
| a=add_expr op=add_op b=mult_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (op, a, b)
  }

%inline add_op:
| PLUS { Plus }
| MINUS { Minus }

mult_expr:
| e=uminus_expr { e }
| a=mult_expr op=mult_op b=uminus_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (op, a, b)
  }

%inline mult_op:
| STAR { Times }
| SLASH { Div }

uminus_expr:
| e=atomic_expr { e }
| MINUS e=atomic_expr  {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_unop (Uminus, e)
  }

atomic_expr:
| LPAREN e=expr RPAREN { e }
| LBRACKET l=app_args RBRACKET {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_array_lit l
}
| n=INT {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_const (C_int (int_of_string n))
  }
| s=QUOTED_STR {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_const (C_string s)
}
| s=COLON_STR {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_const (C_atom s)
}
| v=var {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_var v
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
