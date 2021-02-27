
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

module Trustee_error = struct
  type t = {
    pp: unit Fmt.printer;
    src: exn option;
  }

  exception E of t

  let mk ?src msg : t =
    {pp=(fun out () -> Fmt.string out msg); src}
  let mk_f ?src pp = {pp; src}

  let pp out (e:t) =
    let rec pp_err k src out () =
      k out();
      (match src with
      | None -> ()
      | Some (E e') -> Fmt.fprintf out "@,%a" (pp_err e'.pp e'.src) ()
      | Some e -> Fmt.fprintf out "@,%s" (Printexc.to_string e));
    in
    Fmt.fprintf out  "@[<v>%a@]" (pp_err e.pp e.src) ()
end

let error ?src msg = raise Trustee_error.(E (mk ?src msg))
let errorf ?src k : 'a =
  let pp out () = k (fun fmt ->
      Fmt.kfprintf (fun _o -> ()) out fmt)
  in
  raise (Trustee_error.E{pp; src})

type 'a or_error = ('a, Trustee_error.t) result

let () =
  Printexc.register_printer
    (function
      | Trustee_error.E e ->
        Some (Fmt.to_string Trustee_error.pp e)
      | _ -> None)

let pp_list ?(sep=" ") ppx out l =
  Fmt.list ~sep:(fun out () -> Fmt.fprintf out "%s@," sep) ppx out l
let pp_iter ?(sep=" ") ppx out iter =
  Fmt.iter ~sep:(fun out () -> Fmt.fprintf out "%s@," sep) ppx out iter

module Str_tbl = CCHashtbl.Make(CCString)
module Str_map = CCMap.Make(CCString)
module Str_set = CCSet.Make(CCString)
