open Sigs

type t = {
  name: string;
  chash: Chash.t;
}

let make name chash : t = { name; chash }

let name self = self.name

let chash self = self.chash

let chasher ctx self =
  Chash.string ctx self.name;
  Chash.sub ctx self.chash

let pp_name out self = Fmt.string out self.name

let pp out self = Fmt.fprintf out "%s/%a" self.name Chash.pp self.chash

let to_string self =
  Printf.sprintf "%s/%s" self.name (Chash.to_string self.chash)

let equal a b = String.equal a.name b.name && Chash.equal a.chash b.chash

let compare a b =
  let c = String.compare a.name b.name in
  if c <> 0 then
    c
  else
    Chash.compare a.chash b.chash

let hash self = CCHash.(combine3 129 (string self.name) (Chash.hash self.chash))

let enc enc self =
  Cbor_pack.Enc.(
    add_entry enc @@ list [ text self.name; Chash.enc enc self.chash ])

let dec =
  Cbor_pack.Dec.(
    let key = make_key () in
    memo key
    @@ let* l = list value in
       match l with
       | [ `Text name; chash ] ->
         let+ chash = apply Chash.dec chash in
         { name; chash }
       | _ -> fail "expected cname")
