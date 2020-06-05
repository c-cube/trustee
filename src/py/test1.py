import trustee

ctx = trustee.Ctx()

x = ctx.var('x', ctx.bool())

true_def, true = ctx.basic_def(ctx.eq_app(ctx.var('true', ctx.bool()),
        ctx.eq_app(ctx.lam(x,x), ctx.  lam(x,x))))

ot1 = ctx.parse_ot([
  "../../ot-data/data/opentheory/bool-def-1.11/bool-def.art",
  "../../ot-data/data/opentheory/axiom-extensionality-1.9/axiom-extensionality.art",
  "../../ot-data/data/opentheory/axiom-choice-1.8/axiom-choice.art",
  "../../ot-data/data/opentheory/bool-int-1.18/bool-int.art",
  "../../ot-data/data/opentheory/bool-ext-1.12/bool-ext.art",
  "../../ot-data/data/opentheory/bool-class-1.26/bool-class.art",
  "../../ot-data/data/opentheory/function-def-1.20/function-def.art",
  "../../ot-data/data/opentheory/function-thm-1.49/function-thm.art",
  "../../ot-data/data/opentheory/axiom-infinity-1.12/axiom-infinity.art",
  "../../ot-data/data/opentheory/pair-def-1.24/pair-def.art",
  "../../ot-data/data/opentheory/pair-thm-1.31/pair-thm.art",
  "../../ot-data/data/opentheory/natural-def-1.29/natural-def.art",
  "../../ot-data/data/opentheory/natural-thm-1.22/natural-thm.art",
  #"../../ot-data/data/opentheory/natural-order-def-1.33/natural-order-def.art",
  "../../ot-data/data/opentheory/set-def-1.52/set-def.art",
  #"../../ot-data/data/opentheory/set-thm-1.75/set-thm.art",
  #"../../ot-data/data/opentheory/natural-order-thm-1.41/natural-order-thm.art",
  #"../../ot-data/data/opentheory/natural-add-def-1.25/natural-add-def.art",
    ])


true, def_true = ctx.find('Data.Bool.T')
false, def_false = ctx.find('Data.Bool.F')
exists, def_exists = ctx.find('Data.Bool.?')
forall, def_forall = ctx.find('Data.Bool.!')
not_, def_not = ctx.find('Data.Bool.~')
cond, def_cond = ctx.find('Data.Bool.cond')
pair, def_pair = ctx.find('Data.Pair.,')
fst, def_fst = ctx.find('Data.Pair.fst')
snd, def_snd = ctx.find('Data.Pair.snd')

