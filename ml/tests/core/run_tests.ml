
let () =
  Test_syntax.init();
  Alcotest.run "trustee.core" (Test_help.suite())
