
type view =
  | String of string

type t = {
  view: view;
} [@@unboxed]

let string s : t = {
  view=String s;
}

let view self = self.view
let pp out = function
  | {view=String s} ->
    Fmt.fprintf out "<loc_input=<string (len=%d)>>"
      (String.length s)
