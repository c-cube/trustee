
module Cbor = CBOR.Simple
module CB = Trustee_core.Cbor_pack

let encode (enc:'a CB.Enc.t) (x:'a) : Cbor.t =
  let encoder = CB.Enc.init() in
  let key = enc encoder x in
  let cb = CB.Enc.finalize encoder ~key in
  `Map [
    `Text "h", `Array (Vec.to_list cb.h);
    `Text "k", cb.k;
  ]

let encode_to_string enc x : string =
  Cbor.encode @@ encode enc x

let decode (dec:'a CB.Dec.t) (cbor:Cbor.t) : ('a, _) result =
  match cbor with
  | `Map l ->
    begin match
        let k = try List.assoc (`Text "k") l with _ -> failwith "missing 'k' field" in
        let h = try List.assoc (`Text "h") l with _ -> failwith "missing 'h' field" in
        let h = match h with `Array l-> l | _ -> failwith "'h' field is not a list" in
        {CB.k; h=Vec.of_list h}
      with
      | cb-> CB.Dec.run dec cb
      | exception Failure e -> Error e
    end
  | _ -> Error "expected map"



let decode_string dec (str:string) : _ result =
  match Cbor.decode str with
  | c -> decode dec c
  | exception _ -> Error "invalid CBOR"
