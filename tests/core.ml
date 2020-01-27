
module A = Alcotest
module T = Trustee.Expr
module Thm = Trustee.Thm
module Fmt = CCFormat

let expr_t = A.testable T.pp T.equal
let expr_t_l = A.testable (Fmt.Dump.list T.pp) (CCList.equal T.equal)
let expr_t_set = A.testable Fmt.(map T.Set.elements @@ Dump.list T.pp) T.Set.equal

let test_expr1 =
  A.test_case "expr1" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  if T.equal a b then A.failf "%a and %a must not be equal" T.pp a T.pp b;
  let f = T.new_const "f" T.(u @-> u) in
  let fa1 = T.app f a in
  let fa2 = T.app f a in
  A.check expr_t "hashconsing f should work" fa1 fa2;
  A.check expr_t "type of = is bool" T.bool (T.ty_exn (T.eq a b));
  A.check expr_t "type of = is bool" T.bool (T.ty_exn (T.eq fa1 fa2));
  ()

let test_refl =
  A.test_case "refl" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let f = T.new_const "f" T.(u @-> u) in
  let fa = T.app f a in
  ignore (Thm.refl fa : Thm.t);
  ()

let test_beta =
  A.test_case "beta" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  let f = T.new_const "f" T.(u @-> u) in
  let f2 = T.new_const "f2" T.(u @-> u @-> u) in
  let g = T.new_const "g" T.(u @-> u) in
  let x = T.new_var "x" u in
  let t_lam =
    T.lambda x (T.app f (T.app f (T.app_l f2 [T.var x; T.app (T.lambda x (T.app g (T.var x))) b]))) in
  let thm = Thm.beta t_lam a in
  A.check expr_t "beta reduced"
    (T.eq (T.app t_lam a) @@
     T.app f (T.app f (T.app_l f2 [a; T.app (T.lambda x (T.app g (T.var x))) b])))
    (Thm.concl thm);
  A.check expr_t_set "no hyps" T.Set.empty (Thm.hyps thm);
  ()

(* prove [a=b ==> f a = f b] *)
let test_cong =
  A.test_case "cong" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  let f = T.new_const "f" T.(u @-> u) in
  let fa = T.app f a in
  let fb = T.app f b in
  let thm =
    Thm.cong_fol f [a] [b]
  in
  Format.printf "cong: %a@." Thm.pp thm;
  A.check expr_t "cong result" (T.eq fa fb) (Thm.concl thm);
  ()

(* prove [a=b |- b=a] *)
let test_symm =
  A.test_case "symm" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  (* use leibniz on [λx. a=x] *)
  let p =
    let x = T.new_var "x" u in
    T.lambda x (T.eq (T.var x) a)
  in
  Format.printf "@[<2>a=%a, b=%a, p=%a@]@."
    T.pp_inner a T.pp_inner b T.pp_inner p;
  let thm =
    Thm.eq_leibniz a b ~p |> Thm.cut (Thm.refl a)
  in
  Format.printf "@[<2>symm: %a@]@." Thm.pp thm;
  A.check expr_t "result.concl" (T.eq b a) (Thm.concl thm);
  A.check expr_t_l "result.hyps" [T.eq a b] (T.Set.elements @@ Thm.hyps thm);
  ()

(* prove [a=b |- b=a] *)
let test_symm2 =
  A.test_case "symm2" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  let thm = Trustee.Tier1.eq_sym a b in
  A.check expr_t "result.concl" (T.eq b a) (Thm.concl thm);
  A.check expr_t_l "result.hyps" [T.eq a b] (T.Set.elements @@ Thm.hyps thm);
  ()

(* prove [a=b, b=c |- a=c] *)
let test_trans =
  A.test_case "trans" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  let c = T.new_const "c" u in
  let thm = Trustee.Tier1.eq_trans a b c in
  Format.printf "trans: %a@." Thm.pp thm;
  A.check expr_t "result.concl" (T.eq a c) (Thm.concl thm);
  A.check expr_t_set "result.hyps"
    (T.Set.of_list [T.eq a b; T.eq b c])
    (Thm.hyps thm);
  ()

let test_eq_reflect =
  A.test_case "eq_reflect" `Quick @@ fun () ->
  let u = T.new_const "u" T.type_ in
  let a = T.new_const "a" u in
  let b = T.new_const "b" u in
  let c = T.new_const "c" u in
  let f = T.new_const "f" T.(u @-> u @-> u @-> u @-> u) in
  let thm = Thm.cong_fol f [a; a; b; c] [a; b; b; c] in
  Format.printf "cong_fol: %a@." Thm.pp thm;
  let thm = Trustee.Tier1.eq_reflect thm in
  Format.printf "eq_reflect: %a@." Thm.pp thm;
  A.check expr_t "result.concl"
    (T.eq (T.app_l f [a;a;b;c]) (T.app_l f [a;b;b;c])) (Thm.concl thm);
  A.check expr_t_set "result.hyps"
    (T.Set.of_list [T.eq a b])
    (Thm.hyps thm);
  ()

let suite =
  ["core",
   [test_expr1; test_refl; test_cong; test_symm; test_symm2;
    test_trans; test_eq_reflect; test_beta;
   ]]

let () =
  Alcotest.run "trustee" suite
