type 'a t = {
  mutex: Mutex.t;
  mutable content: 'a;
}

let create content = { mutex = Mutex.create (); content }

let with_lock l f =
  Mutex.lock l.mutex;
  try
    let x = f l.content in
    Mutex.unlock l.mutex;
    x
  with exn ->
    let bt = Printexc.get_raw_backtrace () in
    (match Mutex.unlock l.mutex with
    | () -> Printexc.raise_with_backtrace exn bt
    | exception _ ->
      (* this should only happen if [f …] switched thread *)
      Printf.eprintf "mutex.unlock failed during `with_lock` cleanup\n%!";
      Printexc.raise_with_backtrace (Fun.Finally_raised exn) bt)

let mutex l = l.mutex
let update l f = with_lock l (fun x -> l.content <- f x)

let update_map l f =
  with_lock l (fun x ->
      let x', y = f x in
      l.content <- x';
      y)

let get l =
  Mutex.lock l.mutex;
  let x = l.content in
  Mutex.unlock l.mutex;
  x

let set l x =
  Mutex.lock l.mutex;
  l.content <- x;
  Mutex.unlock l.mutex

let exchange l x =
  Mutex.lock l.mutex;
  let old = l.content in
  l.content <- x;
  Mutex.unlock l.mutex;
  old

module LockRef = struct
  type nonrec 'a t = {
    l: 'a ref;
    mutable usable: bool;
  }

  let as_ref self = self.l
  let get self = !(self.l)

  let set self x =
    assert self.usable;
    self.l := x
end

let with_lock_as_ref l f =
  Mutex.lock l.mutex;
  let lref = { LockRef.l = ref l.content; usable = true } in
  try
    let x = f lref in
    l.content <- !(lref.l);
    lref.usable <- false;
    Mutex.unlock l.mutex;
    x
  with e ->
    l.content <- !(lref.l);
    lref.usable <- false;
    Mutex.unlock l.mutex;
    raise e

let pp ppx out self =
  let x = get self in
  Fmt.fprintf out "(@[lock@ %a@])" ppx x
