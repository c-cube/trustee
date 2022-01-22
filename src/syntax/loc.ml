
module LL = Local_loc

type t = {
  loc: Local_loc.t;
  ctx: Local_loc.ctx;
}

let pp out {ctx; loc} = LL.pp ~ctx out loc
let filename self = self.ctx.LL.filename

let make ~ctx loc : t = {loc; ctx}

let none : t =
  let ctx = LL.create ~filename:"<none>" "" in
  make ~ctx LL.none

let contains {loc;ctx} p =
  let offset = LL.offset_of_pos ~ctx p in
  LL.contains loc ~off:offset

let positions {loc; ctx} = LL.positions ~ctx loc

let union a b : t = {ctx=a.ctx;loc=LL.(a.loc ++ b.loc)}

let union_l a ~f l = List.fold_left (fun l x -> union l (f x)) a l

module Infix = struct
  let (++) = union
end
include Infix
