
module A = Alcotest
module T = Trustee.Expr
module Thm = Trustee.Thm

let expr_t = A.testable T.pp T.equal

let test_expr1 =
  A.test_case "expr1" `Quick @@ fun () ->
  let u = T.new_var "u" T.type_ in
  let a = T.new_var "a" u in
  let b = T.new_var "b" u in
  if T.equal a b then A.failf "%a and %a must not be equal" T.pp a T.pp b;
  let f = T.new_var "f" T.(u @-> u) in
  let fa1 = T.app f a in
  let fa2 = T.app f a in
  A.check expr_t "hashconsing f should work" fa1 fa2;
  A.check expr_t "type of = is bool" T.bool (T.ty_exn (T.eq a b));
  A.check expr_t "type of = is bool" T.bool (T.ty_exn (T.eq fa1 fa2));
  ()

let test_refl =
  A.test_case "refl" `Quick @@ fun () ->
  let u = T.new_var "u" T.type_ in
  let a = T.new_var "a" u in
  let f = T.new_var "f" T.(u @-> u) in
  let fa = T.app f a in
  ignore (Thm.refl fa : Thm.t);
  ()

(* prove [a=b ==> f a = f b] *)
let test_cong =
  A.test_case "refl" `Quick @@ fun () ->
  let u = T.new_var "u" T.type_ in
  let a = T.new_var "a" u in
  let b = T.new_var "b" u in
  let f = T.new_var "f" T.(u @-> u) in
  let fa = T.app f a in
  let fb = T.app f b in
  let thm =
    Thm.cong f [a] [b]
  in
  Format.printf "cong: %a@." Thm.pp thm;
  A.check expr_t "cong result" (T.eq fa fb) (Thm.concl thm);
  ()

let suite =
  ["core", [test_expr1; test_refl; test_cong]]

let () =
  Alcotest.run "trustee" suite
