
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
%type <Ast.lexpr> lexpr
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
| e=top_expr SEMI {
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
| i=block_item_self_delimited bls=block_items { i :: bls }
| i=block_item_atomic SEMI bls=block_items { i :: bls }
| i=block_item_atomic { [ i ] }

(* no need for trailing ; *)
%inline block_item_self_delimited:
| e=brace_expr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_eval e }
| LET v=var EQUAL e=top_expr SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_let (v, e) }
| VAR v=var EQUAL e=top_expr SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_var (v, e) }
| v=var EQUAL e=top_expr SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_assign (v, e) }
| WHILE e=top_expr bl=block {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_while (e,bl) }
| BREAK SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_break }
| CONTINUE SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_continue }
| RETURN e=top_expr SEMI {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_return e }

%inline block_item_atomic:
| e=top_expr_non_brace {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ Bl_eval e }

top_expr:
| e=expr(core_expr) { e }

top_expr_non_brace:
| e=expr(atomic_or_call_expr) { e} 

expr(X):
| e=or_expr(X) { e }

or_expr(X):
| e=and_expr(X) { e }
| a=or_expr(X) OR b=and_expr(X) {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (Or, a, b)
  }

and_expr(X):
| e=bool_expr(X) { e }
| a=and_expr(X) AND b=bool_expr(X) {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (And, a, b)
  }

bool_expr(X):
| e=not_expr(X) { e }
| a=not_expr(X) op=bool_op b=not_expr(X) {
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

not_expr(X):
| e=add_expr(X) { e }
| NOT e=add_expr(X) {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_unop (Not, e)
  }

add_expr(X):
| e=mult_expr(X) { e }
| a=add_expr(X) op=add_op b=mult_expr(X) {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (op, a, b)
  }

%inline add_op:
| PLUS { Plus }
| MINUS { Minus }

mult_expr(X):
| e=uminus_expr(X) { e }
| a=mult_expr(X) op=mult_op b=uminus_expr(X) {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_binop (op, a, b)
  }

%inline mult_op:
| STAR { Times }
| SLASH { Div }

uminus_expr(X):
| e=X { e }
| MINUS e=X  {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_unop (Uminus, e)
  }

core_expr:
| e=atomic_or_call_expr { e}
| e=brace_expr { e }

atomic_or_call_expr:
| e=atomic_expr { e }
| e=call_expr { e }

call_expr:
| f=var LPAREN l=app_args RPAREN {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_app (f, l)
  }

(* atomic (sub)-expression *)
atomic_expr:
| LPAREN e=top_expr RPAREN { e }
| LBRACKET l=app_args RBRACKET {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_array_lit l
}
| DOLLAR le=lexpr DOLLAR {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_logic le
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
  if v.view = "true" then mk ~loc @@ E_const (C_bool true)
  else if v.view = "false" then mk ~loc @@ E_const (C_bool false)
  else mk ~loc @@ E_var v
  }

(* expression ending in {} *)
brace_expr:
| IF e=top_expr bl1=block rest=if_rest {
  let elseif, else_ = rest in
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_if {
    test=e;
    then_=bl1;
    elseif;
    else_;
  }
}
| bl=block {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ E_block bl
}

if_rest:
| { [], None }
| ELSE bl=block { [], Some bl }
| ELSE IF e=top_expr bl=block rest=if_rest {
  let l, else_ = rest in
  (e,bl) :: l, else_ }

app_args:
| { [] }
| e=top_expr { [e] }
| e=top_expr COMMA args=app_args { e :: args }

vars:
|  { [] }
| v=var { [v] }
| v=var COMMA l=vars { v :: l }

var:
| v=IDENT {
  let loc = mk_loc $startpos $endpos in
  (mk ~loc v: A.var)
}

symbol:
| s=SYMBOL {
  let loc = mk_loc $startpos $endpos in
  (mk ~loc s: A.var)
}

(* logic exprs *)

lexpr:
| e=lexpr_app { e }
| binder=lbinder bs=lexpr_binding+ DOT body=lexpr {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_bind { binder; bs; body }
}

%inline lbinder:
| LAMBDA { L_lambda }
| WITH { L_with }
(* TODO
| s=symbol { L_other s }
*)

lexpr_app:
| e=lexpr_atomic { e }
| e=lexpr_symbol { e }
| e=lexpr_atomic l=lexpr_atomic+ {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_app (e,l)
}
| a=lexpr_atomic s=lexpr_symbol b=lexpr_atomic {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_app (s, [a;b])
}
| s=lexpr_symbol e=lexpr_atomic {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_app (s,[e])
}

lexpr_symbol:
| s=symbol {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_var s
}

lexpr_atomic:
| LPAREN e=lexpr RPAREN { e }
| DOLLAR_LBRACE e=top_expr RBRACE {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_escape e
}
| v=var {
  let loc = mk_loc $startpos $endpos in
  mk ~loc @@ L_var v
}

(* variable binding *)
lexpr_binding:
| v=var { [v], None }
| LPAREN vs=var+ COLON e=lexpr RPAREN { vs, Some e }

%%
