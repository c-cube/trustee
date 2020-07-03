set expandtab

syn keyword     trusteeKW        def defconst defthm decl findthm
syn keyword     trusteeKW        findconst set_infix set_binder
syn keyword     trusteeKW        hol_prelude pledge_no_more_axioms source
syn match       trusteeComment "#.*" contains=trusteeTodo

syn match       trusteeSym      +\/[a-zA-Z0-9_]\++


" TODO: handle this only within ``
syn match       trusteeExpr      "let"
syn match       trusteeExpr      "in"
syn match       trusteeExpr      "pi"
syn match       trusteeExpr      "forall"
syn match       trusteeExpr      "exists"
syn match       trusteeExpr      "\~"
syn match       trusteeExpr      "/\\"
syn match       trusteeExpr      "\\/"
syn match       trusteeExpr      "\\\>"
syn match       trusteeExpr      "\."
syn match       trusteeExpr      ":"
syn match       trusteeExpr      "="
syn match       trusteeExpr      "==>"

"syn match       trusteeDelim      "("
"syn match       trusteeDelim      ")"

syn keyword trusteeThm   assume axiom mp bool_eq bool_eq_intro congr
syn keyword trusteeThm   trans refl abs congr_ty beta_conv sym
syn keyword trusteeThm   subst abs

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
  HiLink trusteeSym         String
  HiLink trusteeTodo        Todo
  HiLink trusteeDelim       Delimiter
  delcommand HiLink
end

let b:current_syntax = "trustee"
