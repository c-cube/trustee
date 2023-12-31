type is_done = bool

type 'a t = {
  next: unit -> 'a * Loc.t * is_done;
  mutable cur: 'a;
  mutable loc: Loc.t;
  mutable is_done: is_done;
}

let create ~next () : _ t =
  let cur, loc, is_done = next () in
  { next; cur; loc; is_done }

let is_done self = self.is_done

let cur self = self.cur, self.loc

let consume self =
  if not self.is_done then (
    let cur, loc, is_done = self.next () in
    self.cur <- cur;
    self.loc <- loc;
    self.is_done <- is_done
  )

let next self =
  let r = cur self in
  consume self;
  r

let iter self k =
  let continue = ref true in
  while !continue do
    let t, _loc = cur self in
    k t;
    if is_done self then
      continue := false
    else
      consume self
  done

let to_list self : _ list =
  let l = ref [] in
  iter self (fun t -> l := t :: !l);
  List.rev !l
