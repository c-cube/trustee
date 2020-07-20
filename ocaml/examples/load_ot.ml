
let () =
  let files =
    if Array.length Sys.argv = 1 then
      ["ot-data/data/opentheory/bool-def-1.11/bool-def.art"]
    else Array.to_list @@ Array.sub Sys.argv 1 (Array.length Sys.argv - 1)
  in
  let ctx = Trustee.Ctx.create() in
  let (a,b,c) = Trustee.OpenTheory.parse_ot_files ctx files in
  Array.iter (fun x -> Format.printf "const: %a@." Trustee.Expr.pp x) a;
  Array.iter (fun x -> Format.printf "axiom: %a@." Trustee.Thm.pp x) b;
  Array.iter (fun x -> Format.printf "theorem: %a@." Trustee.Thm.pp x) c;
