open Sigs

module Component = struct
  type t =
    | Str of string
    | Int of int

  let equal a b =
    match a, b with
    | Str a, Str b -> a = b
    | Int a, Int b -> a = b
    | (Str _ | Int _), _ -> false

  let compare a b =
    let to_int_ = function
      | Str _ -> 0
      | Int _ -> 1
    in
    match a, b with
    | Str a, Str b -> String.compare a b
    | Int a, Int b -> Int.compare a b
    | (Str _ | Int _), _ -> Int.compare (to_int_ a) (to_int_ b)

  let hash = function
    | Str a -> CCHash.(combine2 10 (string a))
    | Int a -> CCHash.(combine2 20 (int a))

  let bpf out = function
    | Str s -> Buffer.add_string out s
    | Int i -> Printf.bprintf out "%d" i

  let to_string = function
    | Str s -> s
    | Int i -> string_of_int i
end

type t = {
  path: Component.t list;
  name: Component.t;
}

type sym_ptr = t

let str (n : string) : t =
  assert (not (String.contains n '.'));
  { path = []; name = Str n }

let pos (i : int) : t = { path = []; name = Int i }
let namespace s n : t = { n with path = Str s :: n.path }

let equal a b =
  Component.equal a.name b.name && CCList.equal Component.equal a.path b.path

let hash a =
  CCHash.(combine3 24 (Component.hash a.name) (list Component.hash a.path))

let bpf out self =
  List.iter (fun x -> Printf.bprintf out "%a." Component.bpf x) self.path;
  Component.bpf out self.name

let to_string (self : t) : string =
  match self.path with
  | [] -> Component.to_string self.name
  | _ :: _ ->
    let buf = Buffer.create 32 in
    bpf buf self;
    Buffer.contents buf

let pp out self = Fmt.string out (to_string self)

(* TODO: remove ?
   let parse s =
     let rec loop = function
       | [] -> failwith "empty stanza_id"
       | [s] ->
         (try Pos (int_of_string s) with _ -> Name (Name.make s))
       | s :: x -> Namespace(s, loop x)
     in
     let l = String.split_on_char '.' s in
     loop l
*)

module As_key = struct
  type nonrec t = t

  let equal = equal
  let hash = hash
end

module Tbl = CCHashtbl.Make (As_key)

module Map = struct
  module M = CCMap.Make (Component)

  type 'a t = {
    value: 'a option;
    sub: 'a t M.t;
  }

  let[@inline] mk_ value sub : _ t = { value; sub }
  let empty : _ t = mk_ None M.empty

  let find_sub_exn k self : _ =
    let rec loop ks self =
      match ks with
      | [] -> M.find k.name self.sub
      | k0 :: ks' -> loop ks' (M.find k0 self.sub)
    in
    loop k.path self

  let find_sub k self = try Some (find_sub_exn k self) with Not_found -> None

  let find_exn k self : _ =
    match (find_sub_exn k self).value with
    | Some x -> x
    | None -> raise Not_found

  let find k self = try Some (find_exn k self) with Not_found -> None

  let add k v self : _ t =
    let rec loop ks self =
      match ks with
      | [] ->
        let sub = try M.find k.name self.sub with Not_found -> empty in
        mk_ self.value @@ M.add k.name { sub with value = Some v } self.sub
      | k0 :: ks' ->
        let sub = try M.find k.name self.sub with Not_found -> empty in
        mk_ self.value @@ M.add k0 (loop ks' sub) self.sub
    in
    loop k.path self

  let namespace s self : _ t = mk_ None @@ M.singleton (Component.Str s) self

  let add_with_namespace s ~sub self =
    mk_ self.value @@ M.add (Component.Str s) sub self.sub

  let to_iter (self : _ t) k =
    let rec iter_sub self name k : unit =
      k { path = []; name } self;
      M.iter
        (fun c sub ->
          iter_sub sub c (fun ptr sub ->
              k { ptr with path = name :: ptr.path } sub))
        self.sub
    in
    M.iter
      (fun c sub ->
        iter_sub sub c (fun ptr sub ->
            match sub.value with
            | None -> ()
            | Some v -> k (ptr, v)))
      self.sub
end
