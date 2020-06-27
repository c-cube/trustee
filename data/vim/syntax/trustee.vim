set expandtab

syn keyword     trusteeKW        def defthm decl thm let in
syn match       trusteeComment "#.*" contains=trusteeTodo

"syn match       trusteeDelim      "("
"syn match       trusteeDelim      ")"
syn match       trusteeKW      "\."
syn match       trusteeKW      ":"

syn match       trusteeExpr      "pi"
syn match       trusteeExpr      "forall"
syn match       trusteeExpr      "\~"
syn match       trusteeExpr      "/\\"
syn match       trusteeExpr      "\\/"
syn match       trusteeExpr      "\\\>"

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
  HiLink trusteeTodo        Todo
  HiLink trusteeDelim       Delimiter
  delcommand HiLink
end

let b:current_syntax = "trustee"
