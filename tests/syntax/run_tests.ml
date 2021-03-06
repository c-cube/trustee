
open OUnit2

let test = "trustee.syntax" >::: [
  Test_syntax.suite;
]

let () =
  OUnit2.run_test_tt_main test
