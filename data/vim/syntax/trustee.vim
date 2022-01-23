set expandtab

syn keyword     trusteeKW        def defconst set get decl findthm let defn fn
syn keyword     trusteeKW        expr_ty parse_expr set doc
syn keyword     trusteeKW        findconst set_infix set_binder set_prefix become do eval
syn keyword     trusteeKW        hol_prelude pledge_no_more_axioms source print
syn keyword     trusteeKW        car cdr nil? if else match case fail
syn keyword     trusteeKW        e_app_lhs e_app_rhs e_app e_abs
syn match       trusteeKW        "=="
syn match       trusteeKW        "!="
syn match       trusteeKW        ">="
syn match       trusteeKW        "<="
syn match       trusteeKW        ">"
syn match       trusteeKW        "<"
syn match       trusteeKW        "+"
syn match       trusteeKW        "-"
syn match       trusteeKW        "/"
syn match       trusteeKW        "%"
syn match       trusteeKW        "*"

syn match       trusteeComment "//.*" contains=trusteeTodo

syn match       trusteeStr      +"[^"]\+"+
syn match       trusteeSym      ":[^ \])]\+"
syn match       trusteeSym      "\<true\>"
syn match       trusteeSym      "\<false\>"
syn match       trusteeNum      "\<[0-9]\+\>"

syn region trusteeExprReg  start='\$' end='\$' contains=trusteeExpr

" TODO: handle this only within ``
syn match       trusteeExpr      "\<let\>"
syn match       trusteeExpr      "\<in\>"
syn match       trusteeExpr      "\<with\>"
syn match       trusteeExpr      "\<\\"
syn match       trusteeExpr      "\<forall\>"
syn match       trusteeExpr      "\<exists\>"
syn match       trusteeExpr      "\<T\>"
syn match       trusteeExpr      "\<F\>"
syn match       trusteeExpr      "\<type\>"
syn match       trusteeExpr      "\<bool\>"
syn match       trusteeExpr      "\~"
syn match       trusteeExpr      "/\\"
syn match       trusteeExpr      "\\/"
syn match       trusteeExpr      "\."
syn match       trusteeExpr      ":\>"
syn match       trusteeExpr      "="
syn match       trusteeExpr      "==>"

"syn match       trusteeDelim      "("
"syn match       trusteeDelim      ")"
syn match       trusteeDelim      "\$"

syn keyword trusteeThm   assume axiom mp bool_eq bool_eq_intro congr
syn keyword trusteeThm   trans refl abs absv congr_ty beta_conv sym cut
syn keyword trusteeThm   subst abs rw concl def_ty

syn keyword  trusteeTodo  contained TODO BUG FIX FIXME NOTE

if version >= 508 || !exists("did_trustee_syntax_inits")
  if version < 508
    let did_tptp_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink trusteeComment     Comment
  HiLink trusteeKW          Keyword
  HiLink trusteeExpr        Constant
  HiLink trusteeNum         Constant
  HiLink trusteeThm         Keyword
  HiLink trusteeStr         String
  HiLink trusteeSym         Special
  HiLink trusteeTodo        Todo
  HiLink trusteeDelim       Label
  delcommand HiLink
end

let b:current_syntax = "trustee"
