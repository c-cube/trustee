
open OUnit2

let test = "trustee" >::: [
  Test_kernel.suite;
]

let () =
  OUnit2.run_test_tt_main test
