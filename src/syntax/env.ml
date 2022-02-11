
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
