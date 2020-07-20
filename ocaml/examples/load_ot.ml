
let () =
  let file =
    try Sys.argv.(1) with _ ->
      "ot-data/data/opentheory/bool-def-1.11/bool-def.art"
  in
  let ctx = Trustee.Ctx.create() in
  let (a,b,c) = Trustee.OpenTheory.parse_ot_file ctx file in
  List.iter (fun x -> Format.printf "const: %a@." Trustee.Expr.pp x) a;
  List.iter (fun x -> Format.printf "axiom: %a@." Trustee.Thm.pp x) b;
  List.iter (fun x -> Format.printf "theorem: %a@." Trustee.Thm.pp x) c;
