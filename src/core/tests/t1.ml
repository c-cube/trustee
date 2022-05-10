
open Trustee_core
module CB = Cbor_pack

type cbor = CBOR.Simple.t
let pp_cbor out c = Format.pp_print_string out @@ CBOR.Simple.to_diagnostic c
let pp_vec ppx out v =
  Format.fprintf out "[@[<hv>%a@]]" (Vec.pp ~sep:";" ppx) v

type cbor_pack = CB.t = {
  h: (cbor Vec.t [@printer pp_vec pp_cbor]); (* heap *)
  k: cbor; (* key *)
} [@@deriving show]

type expr =
  | Bool of bool
  | Var of string
  | App of expr * expr
  | Lam of string * expr
  | Let of string * expr * expr
[@@deriving show {with_path=false}, eq]

module E = struct
  let bool b = Bool b
  let true_ = bool true
  let false_ = bool false
  let var s = Var s
  let app1 f a = App (f,a)
  let app f a = List.fold_left app1 f a
  let app' f a = app (var f) a
  let lam v e = Lam (v,e)
  let let_ v e1 e2 = Let (v,e1,e2)
end

type clause = {
  lits: expr list;
}
[@@deriving show {with_path=false}, eq]

let rec enc_expr enc (e:expr) : CB.cbor =
  CB.Enc.(
    match e with
    | Bool b ->
      add_entry enc @@ list [text "b"; bool b]
    | Var s ->
      add_entry enc @@ list [text "v"; text s]
    | App (f,a) ->
      let f = enc_expr enc f in
      let a = enc_expr enc a in
      add_entry enc (list [text "@"; f; a])
    | Lam (v,b) ->
      let b = enc_expr enc b in
      add_entry enc (list [text ">"; text v; b])
    | Let (v,e1,e2) ->
      let e1 = enc_expr enc e1 in
      let e2 = enc_expr enc e2 in
      add_entry enc (list [text "l"; text v; e1; e2])
  )

let dec_expr : expr CB.Dec.t =
  CB.Dec.(
    fix @@ fun self ->
      let* l = list value in
      match l with
      | [`Text "b"; `Bool b] -> return @@ Bool b
      | [`Text "v"; `Text s] -> return @@ Var s
      | [`Text "@"; f; a] ->
        let+ f = apply self f and+ a = apply self a in
        App (f,a)
      | [`Text ">"; `Text v; b] ->
        let+ b = apply self b in
        Lam (v,b)
      | [`Text "l"; `Text v; e1; e2] ->
        let+ e1 = apply self e1 and+ e2 = apply self e2 in
        Let (v, e1, e2)
      | _ -> fail "expected expr"
  )

let enc_clause enc (c:clause) =
  CB.Enc.(
    add_entry enc @@ map [
      text "lits", list (List.map (enc_expr enc) c.lits)
    ]
  )

let dec_clause : clause CB.Dec.t =
  CB.Dec.(
    let+ lits = field "lits" (list dec_expr) in
    {lits}
  )

let c1 = {
  lits=E.[
    let_ "x" true_ (app' "f" [var "x"; var "y"]);
    let_ "x" false_ (app' "g" [app' "g" [var "x"]]);
  ]
}

let () = Format.printf "c1: %a@." pp_clause c1;;

let cb1 = CB.Enc.(let enc = init() in let key = enc_clause enc c1 in finalize enc ~key)

let () = Format.printf "encoded c1: %a@." pp_cbor_pack cb1;;

let c1' = match CB.Dec.run dec_clause cb1 with
  | Ok c -> c
  | Error s -> failwith s;;

let () = Format.printf "dec(enc(c1)): %a@." pp_clause c1';;

let () = assert (equal_clause c1 c1');;

let c1_str = CB.encode_to_string enc_clause c1';;

Format.printf "enc(c1): (len %d) %S@." (String.length c1_str) c1_str;;

let c1'' = match CB.decode_string dec_clause c1_str with
  | Ok c -> c
  | Error e -> failwith e;;

let() = assert (equal_clause c1 c1'')
