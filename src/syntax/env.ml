
open Common_
module TA = Type_ast

type expr = TA.expr
type ty = TA.ty
type const = TA.const
type 'a meta_var = 'a TA.Meta_var.t


type t = {
  consts: const Name.Map.t; (* const -> ty *)
}

let empty = {
  consts=
    Name.Map.empty
    |> Name.Map.add (Name.make "bool") TA.Const.bool;
}

let add_const (c:const) self : t =
  { consts=Name.Map.add c.name c self.consts; }

let find_const n self = Name.Map.find_opt n self.consts

let all_consts self = Name.Map.values self.consts

let pp out (self:t) : unit =
  Fmt.fprintf out "(@[env";
  all_consts self (fun c -> Fmt.fprintf out "@ %a" TA.Const.pp c);
  Fmt.fprintf out "@])"

let completions (self:t) (str:string) : _ Iter.t =
  (* cut a range of the map that has chances of completing [str] *)
  let consts = self.consts in
  let consts =
    let small_enough n =
      let nstr =  Name.to_string n in
      String.compare nstr str < 0
    in
    match Name.Map.find_first_opt small_enough consts with
    | None -> consts
    | Some (n,_) -> let _, _, rhs = Name.Map.split n consts in rhs
  in
  let consts =
    let too_big n =
      let nstr =  Name.to_string n in
      String.compare str nstr < 0 &&
      not (CCString.prefix ~pre:str nstr)
    in
    match Name.Map.find_last_opt too_big consts with
    | None -> consts
    | Some (n,_) -> let lhs,_,_ = Name.Map.split n consts in lhs
  in

  begin
    (* iterate and check *)
    Name.Map.to_iter consts
    |> Iter.filter_map
      (fun (n, c) ->
         let nstr =  Name.to_string n in
         if CCString.prefix ~pre:str nstr then Some c else None)
  end
