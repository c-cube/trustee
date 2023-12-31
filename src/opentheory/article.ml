module K = Trustee_core.Kernel

type t = {
  consts: K.Const.t list;
  axioms: K.Thm.t list;
  theorems: K.Thm.t list;
}

let empty : t = { axioms = []; theorems = []; consts = [] }

type item =
  | I_cst of K.Const.t
  | I_axiom of K.Thm.t
  | I_thm of K.Thm.t

let items self =
  Iter.append_l
    [
      Iter.of_list self.consts |> Iter.map (fun c -> I_cst c);
      Iter.of_list self.axioms |> Iter.map (fun th -> I_axiom th);
      Iter.of_list self.theorems |> Iter.map (fun th -> I_thm th);
    ]

let pp_stats out (self : t) : unit =
  Fmt.fprintf out "(@[%d consts, %d assumptions, %d theorems@])"
    (List.length self.consts) (List.length self.axioms)
    (List.length self.theorems)

let pp_item out = function
  | I_cst c -> Fmt.fprintf out "(@[const %a@])" K.Const.pp c
  | I_axiom th -> Fmt.fprintf out "(@[axiom %a@])" K.Thm.pp_quoted th
  | I_thm th -> Fmt.fprintf out "(@[theorem %a@])" K.Thm.pp_quoted th

let pp out (self : t) =
  Fmt.fprintf out "@[<v2>art {@,%a@;<1 -4>}@]" (Fmt.iter pp_item) (items self)

let to_string = Fmt.to_string pp
