val slice : data:string -> root:int -> string * int
(** Copy the nodes reachable from [root], remapping refs, and return the new
    bytes and root offset. *)

val merge : (string * int) list -> string * int list
(** Concatenate independent slices, remapping their refs, and return the merged
    bytes plus the new roots. Inputs must be [slice] outputs: refs only point to
    earlier nodes, so the remap can be built while emitting. *)
