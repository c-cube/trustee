
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

type t = {
  h: cbor Vec.t; (* heap *)
  k: cbor; (* key *)
}

type cbor_pack = t

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
      | _ -> error path "expected bool"
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
      | _ -> error path "expected map"
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
        Format.asprintf "cbor_pack.Dec.error: %s@ path: %a"
          msg pp_path path in
      Error msg

end


