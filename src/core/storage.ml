
(** Generic storage *)

open Sigs

module type S = sig
  val store : key:string -> ?erase:bool -> 'a Cbor_pack.Enc.t -> 'a -> unit

  val mem : key:string -> bool

  val get : key:string -> 'a Cbor_pack.Dec.t -> 'a option
end

(** Type of a storage implementation *)
type t = (module S)

(** Is [key] in the storage? *)
let mem (self:t) ~key : bool =
  let@ _sp = Tracy.with_ ~file:__FILE__ ~line:__LINE__ ~name:"mem" () in
  let (module M) = self in
  M.mem ~key

(** Get the value for [key] from storage, using [dec] to
    deserialize it *)
let get (self:t) ~key dec : _ option =
  let@ _sp = Tracy.with_ ~file:__FILE__ ~line:__LINE__ ~name:"get" () in
  Tracy.add_text _sp key;
  let (module M) = self in
  M.get ~key dec

(** Store value for [key] in storage.
    @param erase if true, the key is added unconditionally; if false, it
    is added only if not present already (default: false) *)
let store (self:t) ?erase ~key enc x : unit =
  let@ _sp = Tracy.with_ ~file:__FILE__ ~line:__LINE__ ~name:"store" () in
  Tracy.add_text _sp key;
  let (module M) = self in
  M.store ~key ?erase enc x

(** Stores data in an in-memory table *)
let in_memory ?(size=1024) () : t =
  let tbl: string Str_tbl.t = Str_tbl.create size in
  let module M = struct
    let get ~key dec =
      Str_tbl.get tbl key
      |> Option.map (Cbor_pack.decode_string_exn dec)
    let mem ~key = Str_tbl.mem tbl key
    let store ~key ?(erase=false) enc v =
      if erase || not (Str_tbl.mem tbl key) then (
        let v = Cbor_pack.encode_to_string enc v in
        Str_tbl.replace tbl key v
      )
  end
  in (module M)

