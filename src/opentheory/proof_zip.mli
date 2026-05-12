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

(** Load and decode one theory from the zip on demand. Caches result.
    Proof terms are NOT decoded; call [load_proofs] for that. *)
val load_theory : zip_handle -> ctx:K.ctx -> string -> K.Theory.t option

(** Load proof terms for a previously-loaded theory, if available.
    Returns [None] if the entry has no proof section or the theory
    has not been loaded via [load_theory]. *)
val load_proofs : zip_handle -> ctx:K.ctx -> string -> K.Linear_proof.t list option

(** Return a table mapping [expr -> minidag_byte_offset] for the named entry.
    Built lazily; [None] if the entry has not been loaded yet. *)
val expr_offset_table : zip_handle -> string -> int K.Expr.Tbl.t option

(** Decode the expression at a minidag byte offset inside the named entry.
    Fast (cache hit) if the entry is already loaded. *)
val decode_expr_at :
  zip_handle -> ctx:K.ctx -> entry:string -> offset:int -> K.expr option

(** Decode the sequent at a minidag byte offset inside the named entry. *)
val decode_seq_at :
  zip_handle -> ctx:K.ctx -> entry:string -> offset:int -> K.sequent option

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
val load : string -> string Str_tbl.t
val lookup_theory :
  cache:string Str_tbl.t ->
  ctx:K.ctx ->
  string ->
  LP.t list option
