module Fmt = CCFormat

module Make(C : Core.S) = struct
  open C.KoT
  module Goal = Goal.Make(C)
  module T = Expr
  module B = Bool.Make(C)
  module OT = Open_theory.Make(C)

  type t =
    | St_decl of Expr.t
    | St_prove of Goal.t
    | St_load_opentheory of string

  let pp out = function
    | St_decl t -> Fmt.fprintf out "@[<2>decl %a@ : %a@]" T.pp t T.pp (T.ty_exn t)
    | St_prove g -> Fmt.fprintf out "@[<2>prove %a@]" Goal.pp g
    | St_load_opentheory s -> Fmt.fprintf out "opentheory.load %S" s

  module Ctx = struct
    type t = {
      ts: (string, T.t) Hashtbl.t;
      defs: OT.Defs.t;
    }

    let create () : t =
      let self = { ts=Hashtbl.create 32; defs=OT.Defs.create (); } in
      Hashtbl.add self.ts "true" B.true_;
      Hashtbl.add self.ts "false" B.false_;
      Hashtbl.add self.ts "type" T.type_;
      Hashtbl.add self.ts "bool" T.bool;
      self

    let decl self f ~ty =
      let t = Expr.new_const f ty in
      Hashtbl.replace self.ts f t;
      t

    let defs self = self.defs
    let find_exn self f = Hashtbl.find self.ts f
    let find self f = try Some (find_exn self f) with Not_found -> None
    let decl_local self f ~ty =
      let v = Expr.new_var f ty in
      Hashtbl.add self.ts f (Expr.var v);
      v, (fun () -> Hashtbl.remove self.ts f)
  end
  type ctx = Ctx.t

end
