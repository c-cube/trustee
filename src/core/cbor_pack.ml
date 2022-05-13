
module Fmt = CCFormat
module Cbor = CBOR.Simple

type cbor =
  [ `Array of cbor list
  | `Bool of bool
  | `Bytes of string
  | `Float of float
  | `Int of int
  | `Map of (cbor * cbor) list
  | `Null
  | `Simple of int
  | `Tag of int * cbor
  | `Text of string
  | `Undefined ]

(* make sure the types coincide *)
let _ = ignore ((fun x->x):cbor -> Cbor.t)

type t = {
  h: cbor Vec.t; (* heap *)
  k: cbor; (* key *)
}

type cbor_pack = t

let pp out (self:t) : unit =
  Fmt.fprintf out "{@[<v>h=[@[<v>";
  Vec.iteri (fun i v -> Fmt.fprintf out "%d: %s@," i (Cbor.to_diagnostic v)) self.h;
  Fmt.fprintf out "@]];@ k=%s@;<1 -1>@]}" (Cbor.to_diagnostic self.k)

let ptr_tag = 6

module Enc = struct
  type ptr = cbor

  type encoder = {
    eh: cbor Vec.t;
    hashcons: (cbor,ptr) Hashtbl.t;
  }

  type 'a t = encoder -> 'a -> cbor

  let add_entry (self:encoder) x =
    try Hashtbl.find self.hashcons x
    with Not_found ->
      let ptr = `Tag (ptr_tag, `Int (Vec.size self.eh)) in
      Vec.push self.eh x;
      Hashtbl.add self.hashcons x ptr;
      ptr

  let int x : cbor = `Int x
  let bool x : cbor = `Bool x
  let text x : cbor = `Text x
  let blob x : cbor = `Bytes x
  let list x : cbor = `Array x
  let map x : cbor = `Map x

  let init () = {
    eh=Vec.create();
    hashcons=Hashtbl.create 16;
  }

  let finalize (self:encoder) ~key : cbor_pack =
    { h=self.eh; k=key }
end

module Dec = struct
  type path_item =
    | I of int
    | S of string
  type path = path_item list

  let pp_path_item out = function
    | I i -> Format.fprintf out "%d" i
    | S s -> Format.fprintf out "%S" s

  let pp_path out (p:path) =
    Format.pp_print_list ~pp_sep:(fun out () -> Format.fprintf out ".")
      pp_path_item out p

  type 'a t = {
    decode: cbor_pack -> path -> cbor -> 'a
  } [@@unboxed]

  exception Error of path * string
  let error path s = raise (Error (path,s))
  let errorf path fmt = Format.kasprintf (error path) fmt

  (* dereference heap pointer *)
  let rec deref dec path (c:cbor) = match c with
    | `Tag (t, `Int x) when t == ptr_tag ->
      if x < Vec.size dec.h
      then deref dec path (Vec.get dec.h x)
      else errorf path "cannot dereference pointer %d" x
    | c -> c

  let return x = {decode=fun _ _ _ -> x}

  let delay f : _ t = {
    decode=fun dec path c -> (f()).decode dec path c
  }

  let fail s = {
    decode=fun _ path _ -> error path s
  }

  let value = {
    decode=fun dec path c -> deref dec path c
  }

  let int = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Int i -> i
      | _ -> error path "expected int"
  }

  let bool = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Bool b -> b
      | _ -> error path "expected bool"
  }

  let list d = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Array l ->
        List.mapi
          (fun i x -> d.decode dec (I i::path) x)
          l
      | _ -> error path "expected list"
  }

  let map dk dv = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Map l ->
        List.mapi
          (fun i (k,v) -> dk.decode dec path k, dv.decode dec path v)
          l
      | _ -> error path "expected map"
  }

  let text = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Text s -> s
      | _ -> error path "expected text"
  }

  let blob = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Bytes s -> s
      | _ -> error path "expected blob"
  }

  let field (key:string) d = {
    decode=fun dec path c ->
      let c = deref dec path c in
      match c with
      | `Map l ->
        begin match List.assoc (`Text key) l with
          | v -> d.decode dec (S key :: path) v
          | exception Not_found ->
            errorf path "cannot find field %S" key
        end
      | _ -> error path "expected map with string keys"
  }

  let fix f =
    let rec d = {
      decode=fun dec path c ->
        (f d).decode dec path c
    } in
    d

  let apply d c = {
    decode=fun dec path _ -> d.decode dec path c
  }

  let apply_l d cs = {
    decode=fun dec path _ -> List.map (d.decode dec path) cs
  }

  let (let+) x f = {
    decode=fun dec path c ->
      let c = x.decode dec path c in
      f c
  }

  let (let* ) x f = {
    decode=fun dec path c ->
      let xc = x.decode dec path c in
      (f xc).decode dec path c
  }

  let (and+) x y = {
    decode=fun dec path c ->
      let x = x.decode dec path c in
      let y = y.decode dec path c in
      (x,y)
  }

  let run (p:_ t) cb : _ result =
    try Ok (p.decode cb [] cb.k)
    with Error (path, msg) ->
      let msg =
        Format.asprintf "cbor_pack.Dec.error: %s@ (path: %a)@ (in: %a)"
          msg pp_path path pp cb in
      Error msg

end

let encode (enc:'a Enc.t) (x:'a) : Cbor.t =
  let encoder = Enc.init() in
  let key = enc encoder x in
  let cb = Enc.finalize encoder ~key in
  `Map [
    `Text "h", `Array (Vec.to_list cb.h);
    `Text "k", cb.k;
  ]

let cbor_to_string = Cbor.encode

let cbor_of_string = Cbor.decode

let encode_to_string enc x : string =
  Cbor.encode @@ encode enc x

let decode (dec:'a Dec.t) (cbor:Cbor.t) : ('a, _) result =
  match cbor with
  | `Map l ->
    begin match
        let k = try List.assoc (`Text "k") l with _ -> failwith "missing 'k' field" in
        let h = try List.assoc (`Text "h") l with _ -> failwith "missing 'h' field" in
        let h = match h with `Array l-> l | _ -> failwith "'h' field is not a list" in
        {k; h=Vec.of_list h}
      with
      | cb-> Dec.run dec cb
      | exception Failure e -> Error e
    end
  | _ -> Error "expected map"

let decode_string dec (str:string) : _ result =
  match Cbor.decode str with
  | c -> decode dec c
  | exception _ -> Error "invalid CBOR"

let decode_string_exn dec s =
  match decode_string dec s with
  | Ok x -> x
  | Error e -> failwith e
