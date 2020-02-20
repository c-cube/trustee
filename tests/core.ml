
open OUnit2

module Test = struct
  module KoT = Trustee.KoT.Make()
  module Trustee = Trustee.Make(KoT)
  module T = Trustee.Expr
  module Thm = Trustee.Thm
  module Fmt = CCFormat
  module B = Trustee.Bool

  (*
  let expr_t = A.testable T.pp T.equal
  let expr_t_l = A.testable (Fmt.Dump.list T.pp) (CCList.equal T.equal)
  let expr_t_set = A.testable Fmt.(map T.Set.elements @@ Dump.list T.pp) T.Set.equal
     *)

  let t_to_str = Fmt.to_string T.pp
  let tl_to_str = Fmt.to_string (Fmt.Dump.list T.pp)
  let tset_to_str = Fmt.to_string Fmt.(map T.Set.elements @@ Dump.list T.pp)
  let failf msg = Format.kasprintf OUnit2.assert_failure msg

  let tests = ref []
  let add_t what f =
    tests := (what >:: fun _ctx -> f()) :: !tests

  let () = add_t "expr1" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    if T.equal a b then failf "%a and %a must not be equal" T.pp a T.pp b;
    let f = T.new_const "f" T.(u @-> u) in
    let fa1 = T.app f a in
    let fa2 = T.app f a in
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"hashconsing f should work" fa1 fa2;
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"type of = is bool" T.bool (T.ty_exn (T.eq a b));
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"type of = is bool" T.bool (T.ty_exn (T.eq fa1 fa2));
    ()

  let () = add_t "refl" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let f = T.new_const "f" T.(u @-> u) in
    let fa = T.app f a in
    ignore (Thm.refl fa : Thm.t);
    ()

  let () = add_t "beta" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    let f = T.new_const "f" T.(u @-> u) in
    let f2 = T.new_const "f2" T.(u @-> u @-> u) in
    let g = T.new_const "g" T.(u @-> u) in
    let x = T.new_var "x" u in
    let t_lam =
      T.lambda x (T.app f (T.app f (T.app_l f2 [T.var x; T.app (T.lambda x (T.app g (T.var x))) b]))) in
    let thm, _ = Thm.beta t_lam a in
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"beta reduced"
      (T.eq (T.app t_lam a) @@
       T.app f (T.app f (T.app_l f2 [a; T.app (T.lambda x (T.app g (T.var x))) b])))
      (Thm.concl thm);
    assert_equal ~printer:tset_to_str ~cmp:T.Set.equal ~msg:"no hyps"
      T.Set.empty (Thm.hyps thm);
    ()

  (* prove [a=b ==> f a = f b] *)
  let () = add_t "cong" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    let f = T.new_const "f" T.(u @-> u) in
    let fa = T.app f a in
    let fb = T.app f b in
    let thm =
      Thm.congr (Thm.refl f) (Thm.assume (T.eq a b))
    in
    (*   Format.printf "cong: %a@." Thm.pp thm; *)
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"cong result" (T.eq fa fb) (Thm.concl thm);
    ()

  (* prove [a=b |- b=a] *)
  let () = add_t "symm" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    let thm = Trustee.Core.eq_sym a b in
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl" (T.eq b a) (Thm.concl thm);
    assert_equal ~printer:tl_to_str ~cmp:(CCList.equal T.equal) ~msg:"result.hyps"
      [T.eq a b] (T.Set.elements @@ Thm.hyps thm);
    ()

  (* prove the cut rule again *)
  let () = add_t "cut" @@  fun () ->
    let a = T.new_const "a" T.bool in
    let b = T.new_const "b" T.bool in
    let thm = Trustee.Core.cut'
        (Thm.axiom "cut-a" [] a |> fst)
        (Thm.axiom "cut-a->b" [a] b |> fst)
    in
    (*   Format.printf "%a@." Thm.pp thm; *)
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl" b (Thm.concl thm);
    assert_equal ~printer:tl_to_str ~cmp:(CCList.equal T.equal) ~msg:"result.hyps"
      [] (T.Set.elements @@ Thm.hyps thm);
    ()

  (* prove [a=b, b=c |- a=c] *)
  let () = add_t "trans" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    let c = T.new_const "c" u in
    let thm = Trustee.Core.eq_trans a b c in
    (* Format.printf "trans: %a@." Thm.pp thm; *)
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl" (T.eq a c) (Thm.concl thm);
    assert_equal ~printer:tset_to_str ~cmp:T.Set.equal ~msg:"result.hyps"
      (T.Set.of_list [T.eq a b; T.eq b c])
      (Thm.hyps thm);
    ()

  let () = add_t "eq_reflect" @@ fun () ->
    let u = T.new_const "u" T.type_ in
    let a = T.new_const "a" u in
    let b = T.new_const "b" u in
    let c = T.new_const "c" u in
    let f = T.new_const "f" T.(u @-> u @-> u @-> u @-> u) in
    let thm = Trustee.Core.cong_fol f [a; a; b; c] [a; b; b; c] in
    (*   Format.printf "cong_fol: %a@." Thm.pp thm; *)
    let thm = Trustee.Core.eq_reflect thm in
    (*   Format.printf "eq_reflect: %a@." Thm.pp thm; *)
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl"
      (T.eq (T.app_l f [a;a;b;c]) (T.app_l f [a;b;b;c])) (Thm.concl thm);
    assert_equal ~printer:tset_to_str ~cmp:T.Set.equal ~msg:"result.hyps"
      (T.Set.of_list [T.eq a b])
      (Thm.hyps thm);
    ()

  let () = add_t  "eq_true_intro" @@ fun () ->
    let a = T.new_const "a" T.bool in
    let thm = Trustee.Bool.true_eq_intro (Thm.assume a) in
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl"
      (T.eq a B.true_) (Thm.concl thm);
    ()

  let () = add_t "eq_true_elim" @@ fun () ->
    let a = T.new_const "a" T.bool in
    let thm = Trustee.Bool.true_eq_elim (Thm.assume (T.eq a B.true_)) in
    assert_equal ~printer:t_to_str ~cmp:T.equal ~msg:"result.concl" a (Thm.concl thm);
    ()
end

let () =
  let suite = "core" >::: !Test.tests in
  run_test_tt_main suite
