
(** {1 Parser} *)

(* vim:SyntasticToggleMode:
   vim:set ft=yacc: *)

%{
  open Trustee
  module T = Expr
%}

%parameter <PARAM : sig
  val ctx : Statement.ctx
end>

%start <Trustee.Expr.t> parse_term
%start <Statement.t> parse
%start <Statement.t list> parse_list

%left OR
%left AND
%right ARROW

%%

parse_list: l=stmt* EOI {l}
parse: t=stmt EOI { t }
parse_term: t=term EOI { t }

atomic_term:
  | id=IDENT {
    try Statement.Ctx.find_exn PARAM.ctx id
    with Not_found -> failwith (Printf.sprintf "unknown identifier: %s" id)
    }
  | LEFT_PAREN t=term RIGHT_PAREN { t }

bound_var:
  | v=IDENT COLON ty=atomic_term
    { let v, remove = Statement.Ctx.decl_local PARAM.ctx v ~ty in
      v, remove }

app_term:
  | t=atomic_term { t }
  | f=atomic_term l=atomic_term+ { T.app_l f l }

eq_term:
  | t=app_term { t }
  | t=app_term EQ u=app_term { T.eq t u }

binder_term:
  | t=eq_term { t }
  | LAMBDA bv=bound_var DOT body=binder_term
    { let v, remove = bv in remove(); T.lambda v body }
  | PI bv=bound_var DOT body=binder_term
    { let v, remove = bv in remove(); T.pi v body }

prefix_term:
  | t=binder_term { t }
  | NOT t=prefix_term { T.not_ t }

term:
  | t=prefix_term { t }
  | t=term AND u=term { T.and_ t u }
  | t=term OR u=term { T.or_ t u }
  | t=term ARROW u=term { T.arrow t u }

goal:
  | hyps=separated_list(COMMA, term) VDASH concl=term
    { let hyps = List.map (fun t -> "", Thm.assume t) hyps in
      Goal.make ~hyps concl
    }

stmt:
  | ST_DECL f=IDENT COLON ty=term
    { Statement.St_decl (Statement.Ctx.decl PARAM.ctx f ~ty) }
  | ST_PROVE g=goal
    { Statement.St_prove g }

%%
