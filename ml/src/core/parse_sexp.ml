
open Sigs

module K = Kernel

(* TODO: locations *)
type pos = {
  line: int;
  col: int;
}
type loc = {
  start: pos;
  end_: pos;
  file: string;
}
type t = {
  loc: loc;
  view: view
}
and view =
  | Atom of string
  | List of t list

let noloc =
  let p = {line=0;col=0} in
  {start=p; end_=p; file=""}

module Sexp = struct
  include CCSexp.Make(struct
      type nonrec t = t
      type nonrec loc = loc
      let make_loc = Some(fun (l1,c1) (l2,c2) file ->
          {start={line=l1;col=c1};end_={line=l2;col=c2};file})
      let atom_with_loc ~loc s = {loc; view=Atom s}
      let list_with_loc ~loc l = {loc; view=List l}
      let atom = atom_with_loc ~loc:noloc
      let list = list_with_loc ~loc:noloc
      let match_ s ~atom ~list =
        match s.view with
        | Atom s -> atom s
        | List l -> list l
      end)
end

(* TODO: parse S-exprs, port the prelude? *)
(* TODO: port Pratt parser directly? *)

let parse_sexps ctx ~on_expr ~on_thm l : unit =
  let ptop s =
    assert false (* TODO *)
  in
  List.iter ptop l
