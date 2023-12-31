type view =
  | File of string
  | String of string

type t = { view: view } [@@unboxed]

let file s : t = { view = File s }

let string s : t = { view = String s }

let view self = self.view

let pp out = function
  | { view = File s } -> Fmt.fprintf out "<loc_input=<file %S>>" s
  | { view = String s } ->
    Fmt.fprintf out "<loc_input=<string (len=%d)>>" (String.length s)
