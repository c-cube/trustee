open Trustee_opentheory
open Common_

type t = {
  lock: Mutex.t;
  ctx: K.Ctx.t;
  idx: Idx.t;
  eval: Eval.state;
  proof_cache: (string, string) Hashtbl.t option;
      (** In-memory zip cache loaded from a --proof-zip file, if any. *)
}

let create ?cb ?progress_bar ?proof_zip ~ctx ~idx () : t =
  let eval = Eval.create ?cb ?progress_bar ~ctx ~idx () in
  let proof_cache =
    match proof_zip with
    | None -> None
    | Some path ->
      (try
         let tbl = Proof_zip.load path in
         Fmt.printf "loaded proof zip: %s (%d entries)@." path
           (Hashtbl.length tbl);
         Some tbl
       with e ->
         Fmt.eprintf "warning: could not load proof zip %s: %s@." path
           (Printexc.to_string e);
         None)
  in
  { lock = Mutex.create (); ctx; idx; eval; proof_cache }

let[@inline] with_lock l f =
  Mutex.lock l;
  Fun.protect ~finally:(fun () -> Mutex.unlock l) f
