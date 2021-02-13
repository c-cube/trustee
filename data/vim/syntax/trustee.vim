
set expandtab

syn keyword     tprfKW    def declare axiom show expr proof end fixity goal subst
syn keyword     tprfKW    theorem by
syn keyword     tprfKW    let in

syn keyword tprfPrim   assume axiom mp bool_eq bool_eq_intro congr
syn keyword tprfPrim   trans refl abs absv congr_ty beta_conv sym cut
syn keyword tprfPrim   inst abs rw concl def_ty


syn match       tprfComment "#.*" contains=tprfTodo

syn match       tprfStr      +"[^"]\+"+
syn match       tprfSym      "\<true\>"
syn match       tprfSym      "\<false\>"
syn match       tprfNum      "\<[0-9]\+\>"

syn match       tprfExpr      "\<pi\>"
syn match       tprfExpr      "\<with\>"
syn match       tprfExpr      "\<\\"
syn match       tprfExpr      "\<forall\>"
syn match       tprfExpr      "\<exists\>"
syn match       tprfExpr      "\<T\>"
syn match       tprfExpr      "\<F\>"
syn match       tprfExpr      "\~"
syn match       tprfExpr      "/\\"
syn match       tprfExpr      "\\/"
syn match       tprfExpr      "\."
syn match       tprfExpr      "="
syn match       tprfExpr      "==>"

syn match       tprfType      "\<type\>"
syn match       tprfType      "\<bool\>"

syn match       tprfSpecial ":"
syn match       tprfSpecial ":="

syn match       tprfDelim      "("
syn match       tprfDelim      ")"

syn keyword  tprfTodo  contained TODO BUG FIX FIXME NOTE

if version >= 508 || !exists("did_tprf_syntax_inits")
  if version < 508
    let did_tptp_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink tprfComment     Comment
  HiLink tprfKW          Keyword
  HiLink tprfExpr        Constant
  HiLink tprfNum         Constant
  HiLink tprfPrim        Constant
  HiLink tprfStr         String
  HiLink tprfSym         Special
  HiLink tprfTodo        Todo
  HiLink tprfType        Type
  HiLink tprfDelim       Delimiter
  HiLink tprfSpecial     Special
  delcommand HiLink
end

let b:current_syntax = "tprf"
