open OUnit2

let test =
  "trustee"
  >::: [
         Test_kernel.suite;
         Test_unif.suite;
         Test_kbo.suite;
         Test_rw.suite;
         Test_cc.suite;
       ]

let () = OUnit2.run_test_tt_main test
