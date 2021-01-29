
open Sigs

type loc = Loc.t
type is_done = bool
type 'a t = {
  next:(unit -> 'a * loc * is_done);
  mutable cur: 'a;
  mutable loc: loc;
  mutable is_done: is_done;
}

let create ~next () : _ t =
  let cur, loc, is_done = next() in
  {next; cur; loc; is_done;}

let is_done self = self.is_done
let cur self = self.cur, self.loc

let junk self =
  if not self.is_done then (
    let cur, loc, is_done = self.next() in
    self.cur <- cur; self.loc <- loc; self.is_done <- is_done;
  )

let next self =
  let r = cur self in
  junk self;
  r

let to_list self : _ list =
  let l = ref [] in
  let continue = ref true in
  while !continue do
    let t, _loc = cur self in
    l := t :: !l;
    if is_done self then continue := false else junk self;
  done;
  List.rev !l
