open Common_
module TA = Type_ast

type expr = TA.expr
type ty = TA.ty
type const = TA.const
type 'a meta_var = 'a TA.Meta_var.t
type t = { consts: const Str_map.t (* const -> ty *) }

let empty = { consts = Str_map.empty |> Str_map.add "bool" TA.Const.bool }

let add_const (c : const) self : t =
  { consts = Str_map.add c.name c self.consts }

let find_const n self = Str_map.find_opt n self.consts
let all_consts self = Str_map.values self.consts

let pp out (self : t) : unit =
  Fmt.fprintf out "(@[env";
  all_consts self (fun c -> Fmt.fprintf out "@ %a" TA.Const.pp c);
  Fmt.fprintf out "@])"

let completions (self : t) (str : string) : _ Iter.t =
  (* cut a range of the map that has chances of completing [str] *)
  let consts = self.consts in
  let consts =
    let small_enough n = String.compare n str < 0 in
    match Str_map.find_first_opt small_enough consts with
    | None -> consts
    | Some (n, _) ->
      let _, _, rhs = Str_map.split n consts in
      rhs
  in
  let consts =
    let too_big n =
      String.compare str n < 0 && not (CCString.prefix ~pre:str n)
    in
    match Str_map.find_last_opt too_big consts with
    | None -> consts
    | Some (n, _) ->
      let lhs, _, _ = Str_map.split n consts in
      lhs
  in

  (* iterate and check *)
  Str_map.to_iter consts
  |> Iter.filter_map (fun (n, c) ->
         if CCString.prefix ~pre:str n then
           Some c
         else
           None)
