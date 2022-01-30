
open Sigs

module type S = Error_intf.S
module type LOC = Error_intf.LOC

module Make(Loc : LOC) : S with type loc = Loc.t = struct
  type loc = Loc.t
  type t = {
    msg: unit -> string;
    ctx_of: t option;
    loc: loc option;
  }

  type 'a or_error = ('a, t) result

  exception E of t
  let raise x = raise (E x)

  let msg self = self.msg()
  let msg' self = self.msg
  let loc self = self.loc
  let ctx_of self = self.ctx_of

  let unwrap_ctx self =
    let rec aux acc self = match self.ctx_of with
      | None -> self, acc
      | Some e -> aux (self::acc) e
    in
    aux [] self

  let make' ?loc msg = {msg; loc; ctx_of=None }
  let make ?loc msg : t = make' ?loc (fun () -> msg)
  let makef ?loc fmt = Fmt.kasprintf (make ?loc) fmt

  let of_exn exn =
    match exn with
    | E e -> e
    | _ ->
      let res = Printf.sprintf "%s\n%s"
          (Printexc.to_string exn) (Printexc.get_backtrace ())
      in
      make res

  let wrap' ?loc msg e = { msg; loc; ctx_of=Some e }
  let wrap ?loc msg e = wrap' ?loc (fun () -> msg) e
  let wrapf ?loc fmt = Fmt.kasprintf (wrap ?loc) fmt

  let fail' ?loc msg = raise (make' ?loc msg)
  let fail ?loc msg = raise (make ?loc msg)
  let failf ?loc k =
    let msg () =
      let r = ref "" in
      k (fun fmt -> Fmt.kasprintf (fun s ->  r:= s) fmt);
      !r
    in
    fail' ?loc msg

  let[@inline] guard wrap f =
    try f()
    with
    | E e -> raise (wrap e)
    | exn -> raise (wrap (of_exn exn))

  let unwrap = function
    | Ok x -> x
    | Error e -> raise e

  let unwrap_opt' msg = function
    | Some x -> x
    | None -> fail (msg())

  let unwrap_opt msg o = unwrap_opt' (fun()->msg) o

  let hbar = String.make 60 '-'

  let pp out (self:t) =
    let pp_itself out self =
      let {msg; loc; ctx_of=_} = self in
      let msg=msg() in
      match loc with
      | None -> Fmt.string_lines out msg
      | Some loc ->
        Fmt.fprintf out "@[<v>%a@,%a@]"
          Fmt.string_lines msg Loc.pp loc
    in
    let rec loop out self =
      begin match self.ctx_of with
        | None -> Fmt.fprintf out "@[<v2>@{<Red>Error@}:@ %a@]" pp_itself self
        | Some e ->
          Fmt.fprintf out "%a@,%s@,@[<v2>@{<Blue>Context@}:@ %a@]"
            loop e hbar pp_itself self
      end
    in
    Fmt.fprintf out "@[<v>%a@]" loop self

end

module Conv(E : S)(E2 : S)(Conv : sig val conv : E.loc -> E2.loc option end) = struct
  let rec conv e : E2.t =
    let msg = E.msg' e in
    let loc = E.loc e in
    let ctx_of = E.ctx_of e in
    let loc = Option.flat_map Conv.conv loc in
    begin match ctx_of with
      | None -> E2.make' ?loc msg
      | Some err2 -> E2.wrap' ?loc msg (conv err2)
    end
end

include Make(struct type t = unit let pp _out () = () end)
