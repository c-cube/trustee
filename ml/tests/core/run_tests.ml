
let suite =
  [ Test_syntax.suite;
  ]

let () =
  Alcotest.run "trustee.core" suite
