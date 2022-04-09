
open Trustee_opentheory
open Common_

type t = {
  lock: Mutex.t;
  idx: Idx.t;
  eval: Eval.state;
}

let create ?cb ?progress_bar ~ctx ~idx () : t =
  let eval = Eval.create ?cb ?progress_bar ~ctx ~idx () in
  { lock=Mutex.create(); idx; eval; }

let[@inline] with_lock l f =
  Mutex.lock l;
  Fun.protect ~finally:(fun () -> Mutex.unlock l) f
