(** Generic storage — raw string keys/values *)

open Sigs

module type S = sig
  val store : key:string -> ?erase:bool -> string -> unit
  val mem : key:string -> bool
  val get : key:string -> string option
end

type t = (module S)
(** Type of a storage implementation *)

(** Is [key] in the storage? *)
let mem (self : t) ~key : bool =
  let (module M) = self in
  M.mem ~key

(** Get the raw bytes for [key] from storage *)
let get (self : t) ~key : string option =
  let (module M) = self in
  M.get ~key

(** Store raw bytes for [key] in storage.
    @param erase
      if true, the key is added unconditionally; if false, it is added only if
      not present already (default: false) *)
let store (self : t) ?erase ~key (s : string) : unit =
  let (module M) = self in
  M.store ~key ?erase s

(** Stores data in an in-memory table *)
let in_memory ?(size = 1024) () : t =
  let tbl : string Str_tbl.t = Str_tbl.create size in
  let module M = struct
    let get ~key = Str_tbl.get tbl key

    let mem ~key = Str_tbl.mem tbl key

    let store ~key ?(erase = false) s =
      if erase || not (Str_tbl.mem tbl key) then
        Str_tbl.replace tbl key s
  end in
  (module M)
