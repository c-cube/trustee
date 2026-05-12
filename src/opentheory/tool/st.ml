open Trustee_opentheory
open Common_

type t = {
  lock: Mutex.t;
  ctx: K.Ctx.t;
  idx: Idx.t;
  eval: Eval.state;
  zip: Proof_zip.zip_handle option;
}

let create ?cb ?progress_bar ?proof_zip ~ctx ~idx () : t =
  let eval = Eval.create ?cb ?progress_bar ~ctx ~idx () in
  let zip =
    match proof_zip with
    | None -> None
    | Some path ->
      (try
         let zh = Proof_zip.open_zip path in
         Fmt.printf "opened proof zip: %s (%d theories)@." path
           (List.length (Proof_zip.theory_names zh));
         Proof_zip.restore_storage zh ctx;
         Some zh
       with e ->
         Fmt.eprintf "error opening proof zip %s: %s@." path
           (Printexc.to_string e);
         None)
  in
  { lock = Mutex.create (); ctx; idx; eval; zip }

let[@inline] with_lock l f =
  Mutex.lock l;
  Fun.protect ~finally:(fun () -> Mutex.unlock l) f

(** Load a theory from zip (caches in zip_handle's theory_cache).
    Also populates [idx.by_name] with the theory's consts and thms. *)
let load_theory (self : t) (name : string) : K.Theory.t option =
  match self.zip with
  | None -> None
  | Some zh ->
    (match Proof_zip.load_theory zh ~ctx:self.ctx name with
    | None -> None
    | Some th as result ->
      (* Populate by_name so /c/<name> works for visited theories *)
      let all_consts =
        K.Theory.param_consts th @ K.Theory.consts th
      in
      List.iter
        (fun c ->
          Str_tbl.replace self.idx.Idx.by_name (K.Const.name c)
            (Idx.H_const c))
        all_consts;
      List.iter
        (fun thm ->
          let key = Fmt.to_string K.Thm.pp thm in
          Str_tbl.replace self.idx.Idx.by_name key (Idx.H_thm thm))
        (K.Theory.param_theorems th @ K.Theory.theorems th);
      result)
