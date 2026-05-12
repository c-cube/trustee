(** Proof-trace zip archive.

    One zip entry per theory (keyed by theory name), containing the minidag-
    encoded [Linear_proof.t] list for all theorems defined by that theory. *)

open Common_

val zip_entry_name : string -> string
(** [zip_entry_name theory_name] returns the zip entry name for a theory. *)

val build :
  output:string ->
  eval:Eval.state ->
  names:string Iter.t ->
  unit
(** [build ~output ~eval ~names] evaluates every theory in [names],
    linearises the proof of every theorem defined by each theory, encodes them
    as minidag, and stores them as a zip archive at [output]. *)

val load : string -> (string, string) Hashtbl.t
(** [load path] opens the zip archive at [path] and returns a table mapping
    zip entry name -> raw minidag bytes. *)

val lookup_theory :
  cache:(string, string) Hashtbl.t ->
  ctx:K.ctx ->
  string ->
  K.Linear_proof.t list option
(** [lookup_theory ~cache ~ctx name] decodes the proof list for theory [name]
    from the in-memory cache, or returns [None] if not present. *)
