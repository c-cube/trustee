
open Sigs

module K = Kernel

type position = Position.t lazy_t

type t = {
  pos: position;
  view: view;
}

and ty = t

and var = {
  v_name: string;
  v_ty: ty option;
  v_kind: var_kind
}

and var_kind =
  | V_normal
  | V_at
  | V_question_mark

and binding = var * t

and view =
  | Type
  | Ty_arrow of ty * ty
  | Ty_pi of var list * ty
  | Var of var
  | Meta of {
      name: string;
      ty: ty;
      mutable deref: t option;
    }
  | Const of {
      c: K.Expr.t;
      at: bool; (* explicit types? *)
    }
  | App of t * t list
  | Lambda of var list * t
  | Bind of K.Expr.t * var list * t
  | With of var list * t
  | Eq of t * t
  | Let of binding list * t

let nopos: position = lazy Position.none

let rec pp out (e:t) : unit =
  match e.view with
  | Type -> Fmt.string out "type"
  | Var v -> Fmt.string out v.v_name
  | Ty_arrow (a,b) ->
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a pp b;
  | Ty_pi (vars, bod) ->
    Fmt.fprintf out "(@[pi %a.@ %a@])"
      (pp_list pp_var) vars pp bod
  | Const {c;at} ->
    let s = if at then "@" else "" in
    Fmt.fprintf out "%s%a" s K.Expr.pp c
  | App (f,l) -> Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_list pp) l
  | Meta v -> Fmt.fprintf out "?%s" v.name
  | Lambda (vars,bod) ->
    Fmt.fprintf out "(@[fn %a.@ %a@])" (pp_list pp_var_ty) vars pp bod
  | Bind (c, vars,bod) ->
    Fmt.fprintf out "(@[%a %a.@ %a@])"
      K.Expr.pp c (pp_list pp_var_ty) vars pp bod
  | With (vars,bod) ->
    Fmt.fprintf out "(@[with %a.@ %a@])" (pp_list pp_var_ty) vars pp bod
  | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
  | Let (bs,bod) ->
    let pp_b out (v,e) : unit = Fmt.fprintf out "@[%s@ = %a@]" v.v_name pp e in
    Fmt.fprintf out "(@[let %a in@ %a@])" (pp_list ~sep:" and " pp_b) bs pp bod
and pp_atom_ out e =
  match e.view with
  | Type | Var _ | Meta _ | Const _ -> pp out e
  | _ -> Fmt.fprintf out "(@[%a@])" pp e
and pp_var out v = Fmt.string out v.v_name
and pp_var_ty out (v:var) : unit =
  match v.v_ty with
  | None -> Fmt.string out v.v_name
  | Some ty -> Fmt.fprintf out "(@[%s@ : %a@])" v.v_name pp ty

module Var = struct
  type t = var
  let make ?kind:(v_kind=V_normal) v_name v_ty : var = {v_name; v_ty; v_kind}

  let pp out v = Fmt.string out v.v_name
  let pp_with_ty = pp_var_ty
end

let mk_ ?(pos=nopos) view : t = {view; pos=pos}

let[@inline] view e = e.view
let[@inline] pos e = Lazy.force e.pos
let pp = pp

let type_ : t = mk_ Type
let ty_var ?pos s : t = mk_ ?pos (Var (Var.make s (Some type_)))
let ty_meta ?pos (s:string) : ty = mk_ ?pos (Meta {deref=None; ty=type_; name=s})
let ty_arrow ?pos a b : ty = mk_ ?pos (Ty_arrow (a,b))
let ty_pi ?pos vars bod : ty = match vars with
  | [] -> bod
  | _ -> mk_ ?pos (Ty_pi (vars, bod))

let var ?pos (v:var) : t = mk_ ?pos (Var v)
let const ?pos ?(at=false) c : t = mk_ ?pos (Const {c; at})
let meta ?pos (s:string) ty : t = mk_ ?pos (Meta {deref=None; ty; name=s})
let app ?pos (f:t) (l:t list) : t =
  match f.view with
  | App (f1,l1) -> mk_ ?pos (App (f1,l1@l))
  | _ -> mk_ ?pos (App (f,l))
let let_ ?pos bs bod : t = mk_ ?pos (Let (bs, bod))
let with_ ?pos vs bod : t = mk_ ?pos (With (vs, bod))
let lambda ?pos vs bod : t = mk_ ?pos (Lambda (vs, bod))
let bind ?pos c vs bod : t = mk_ ?pos (Bind (c, vs, bod))
let eq ?pos a b : t = mk_ ?pos (Eq (a,b))

let to_string = Fmt.to_string @@ Fmt.hvbox pp

(* TODO *)
let ty_infer _ctx _e : K.Expr.t =
  assert false

