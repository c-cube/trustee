
val storage : string -> Storage.t
(** Use the given filename to provide storage using Sqlite *)

val storage_xdg_cache : unit -> Storage.t
(** Use the XDG cache directory to provide storage using Sqlite *)
