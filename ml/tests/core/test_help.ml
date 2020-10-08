
module A = Alcotest

let tests : (string, unit A.test_case list) Hashtbl.t = Hashtbl.create 32

let add sec (l0:_ list) =
  let l = try Hashtbl.find tests sec with Not_found -> [] in
  Hashtbl.replace tests sec (l0 @ l)

let suite() : unit A.test list =
  CCHashtbl.to_list tests
