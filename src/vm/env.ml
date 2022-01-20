module Str_map = Str_map

type value = Value.t

type t = {
  vals: value Str_map.t;
  parent: t option;
}

let empty = { vals=Str_map.empty; parent=None }
let parent self = self.parent

let add self s v = {self with vals=Str_map.add s v self.vals}

let[@unroll 2] rec find self s =
  match Str_map.find_opt s self.vals with
  | Some _ as v -> v
  | None ->
    begin match parent self with
      | None -> None
      | Some p -> find p s
    end
