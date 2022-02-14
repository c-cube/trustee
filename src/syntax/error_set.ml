
(** Error set.

    An object can contain (reified) errors. For example at parsing, we
    do not fail if a parse error occurs; we try to recover and emit an
    "error" node with the location the parsing error occurred.

    This makes the whole system more robust to partial or incorrect inputs,
    i.e. most inputs in the LSP server.

    The error set concept comes later, once we have processed a buffer: we
    want to collect all the errors that occurred, and display them back
    to the user. In batch mode we just print all the errors in the same way.
*)

open Common_

(** An object with a set of errors inside. *)
class virtual t = object
  method virtual iter_errors : (Loc.t * Error.t) Iter.t
  (** Iterate on errors contained in this *)
end

let[@inline] iter_errors (self:t) : (Loc.t * Error.t) Iter.t =
  fun f -> self#iter_errors f

(** Merge a list of error sets together *)
let merge_l (l:t list) : t =
  object method iter_errors f = List.iter (fun x -> x#iter_errors f) l end

(** Merge a list of error sets together *)
let merge_seq (l:t Seq.t) : t =
  object method iter_errors f = CCSeq.iter (fun x -> x#iter_errors f) l end

let merge (a:t) (b:t) : t =
  object method iter_errors f = a#iter_errors f; b#iter_errors f end

module Syntax = struct
  (** Alias for {!merge} *)
  let (++) = merge
end

include Syntax
