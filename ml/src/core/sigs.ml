
module Fmt = CCFormat

type 'a iter = ('a -> unit) -> unit

module type EQ = sig
  type t
  val equal : t -> t -> bool
end

module type COMPARE = sig
  type t
  val compare : t -> t -> int
end

module type HASH = sig
  type t
  val hash : t -> int
end

module type PP = sig
  type t
  val pp : t Fmt.printer
  val to_string : t -> string
end

exception Trustee_error of unit Fmt.printer * exn option

let error ?src msg = raise (Trustee_error ((fun out () -> Fmt.string out msg), src))
let errorf ?src k : 'a =
  let pp out () = k (fun fmt ->
      Fmt.kfprintf (fun _o -> ()) out fmt)
  in
  raise (Trustee_error (pp, src))

let () =
  let rec pp_err k src out () =
    k out();
    (match src with
    | None -> ()
    | Some (Trustee_error (k,ctx)) -> pp_err k ctx out ()
    | Some e -> Fmt.fprintf out "@,%s" (Printexc.to_string e));
  in
  Printexc.register_printer
    (function
      | Trustee_error (k, ctx) ->
        Some (Fmt.asprintf "@[<v>%a@]" (pp_err k ctx) ())
      | _ -> None)

let pp_list ?(sep=" ") ppx out l =
  Fmt.list ~sep:(fun out () -> Fmt.fprintf out "@;%s" sep) ppx out l

module Str_tbl = CCHashtbl.Make(CCString)
