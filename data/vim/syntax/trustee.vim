set expandtab

syn keyword     trusteeKW        def defconst defthm decl findthm let defn
syn keyword     trusteeKW        findconst set_infix set_binder
syn keyword     trusteeKW        hol_prelude pledge_no_more_axioms source
syn keyword     trusteeKW        pstack clear swap rot begin end
syn match       trusteeComment ";.*" contains=trusteeTodo

syn match       trusteeStr      +"[^"]\+"+
syn match       trusteeSym      ":[^ \])]\+"


" TODO: handle this only within ``
syn match       trusteeExpr      "\blet\b"
syn match       trusteeExpr      "\bin\b"
syn match       trusteeExpr      "\bpi\b"
syn match       trusteeExpr      "\bforall\b"
syn match       trusteeExpr      "\bexists\b"
syn match       trusteeExpr      "\~"
syn match       trusteeExpr      "/\\"
syn match       trusteeExpr      "\\/"
syn match       trusteeExpr      "\\\>"
syn match       trusteeExpr      "\."
syn match       trusteeExpr      ":\>"
syn match       trusteeExpr      "="
syn match       trusteeExpr      "==>"

"syn match       trusteeDelim      "("
"syn match       trusteeDelim      ")"

syn keyword trusteeThm   assume axiom mp bool_eq bool_eq_intro congr
syn keyword trusteeThm   trans refl abs abs_expr congr_ty beta_conv sym
syn keyword trusteeThm   subst abs rw concl

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
  HiLink trusteeThm         Keyword
  HiLink trusteeStr         String
  HiLink trusteeSym         Special
  HiLink trusteeTodo        Todo
  HiLink trusteeDelim       Delimiter
  delcommand HiLink
end

let b:current_syntax = "trustee"
