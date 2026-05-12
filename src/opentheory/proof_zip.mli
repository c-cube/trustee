(** Proof-trace zip archive.

    Contains:
    - ["_storage/<key>"] entries: one per const-def storage key
    - ["<name>.entry"] per theory: minidag of consts + thm sequents *)

open Common_

module Storage = Trustee_core.Storage
module LP = K.Linear_proof

(** A storage wrapper that records all (key, bytes) stored into it.
    Create one before building the ctx; use [tracked_as_storage] to get
    the storage to pass to [K.Ctx.create]; then pass [ts] to [build]. *)
type tracked_storage

val make_tracked_storage : ?size:int -> unit -> tracked_storage
val tracked_as_storage : tracked_storage -> Storage.t

(** A handle to an open zip file for server-side on-demand loading. *)
type zip_handle

val open_zip : string -> zip_handle
val close_zip : zip_handle -> unit
val theory_names : zip_handle -> string list

(** Restore const-def storage from the zip's [_storage/*] entries into ctx. *)
val restore_storage : zip_handle -> K.ctx -> unit

(** Load and decode one theory from the zip on demand. Caches result. *)
val load_theory : zip_handle -> ctx:K.ctx -> string -> K.Theory.t option

(** Build a zip file from all theories.
    [ts] must be the tracked storage used when creating the ctx.
    [eval] must be the eval state that evaluated all the theories. *)
val build :
  output:string ->
  eval:Eval.state ->
  ts:tracked_storage ->
  names:string Iter.t ->
  unit

(** Legacy API for backward compatibility. *)
val zip_entry_name : string -> string
val encode_proof_list : LP.t list -> string
val decode_proof_list : K.ctx -> string -> LP.t list
val load : string -> (string, string) Hashtbl.t
val lookup_theory :
  cache:(string, string) Hashtbl.t ->
  ctx:K.ctx ->
  string ->
  LP.t list option
