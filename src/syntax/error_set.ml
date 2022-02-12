
open Common_

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
