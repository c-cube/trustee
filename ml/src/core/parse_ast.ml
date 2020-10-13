
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
  | Ty_meta of {
      name: string;
      mutable v: ty option;
    }
  | Ty_pi of string list * ty
  | Var of var
  | Const of K.Expr.t
  | App of t * t list
  | Lambda of var list * t
  | With of var list * t
  | Eq of t * t
  | Let of binding list * t

let nopos: position = lazy Position.none

let rec pp out (e:t) : unit =
  match e.view with
  | Type -> Fmt.string out "type"
  | Var v -> Fmt.string out v.v_name
  | Ty_meta v -> Fmt.fprintf out "?%s" v.name
  | Ty_arrow (a,b) ->
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a pp b;
  | Ty_pi (vars, bod) ->
    Fmt.fprintf out "(@[pi %a.@ %a@])"
      (pp_list Fmt.string) vars pp bod
  | Const c -> K.Expr.pp out c
  | App (f,l) -> Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_list pp) l
  | Lambda (vars,bod) ->
    Fmt.fprintf out "(@[fn %a.@ %a@])" (pp_list pp_var_ty) vars pp bod
  | With (vars,bod) ->
    Fmt.fprintf out "(@[with %a.@ %a@])" (pp_list pp_var_ty) vars pp bod
  | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
  | Let (bs,bod) ->
    let pp_b out (v,e) : unit = Fmt.fprintf out "@[%s@ = %a@]" v.v_name pp e in
    Fmt.fprintf out "(@[let %a in@ %a@])" (pp_list pp_b) bs pp bod
and pp_atom_ out e =
  match e.view with
  | Type | Var _ | Ty_meta _ | Const _ -> pp out e
  | _ -> Fmt.fprintf out "(@[%a@])" pp e
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

let[@inline] pos e = Lazy.force e.pos
let pp = pp

let type_ : t = mk_ Type
let ty_var ?pos s : t = mk_ ?pos (Var (Var.make s (Some type_)))
let ty_meta ?pos (s:string) : ty = mk_ ?pos (Ty_meta {v=None; name=s})
let ty_arrow ?pos a b : ty = mk_ ?pos (Ty_arrow (a,b))
let ty_pi ?pos vars bod : ty = match vars with
  | [] -> bod
  | _ -> mk_ ?pos (Ty_pi (vars, bod))

let var ?pos (v:var) : t = mk_ ?pos (Var v)
let const ?pos c : t = mk_ ?pos (Const c)
let app ?pos (f:t) (l:t list) : t = mk_ ?pos (App (f,l))
let let_ ?pos bs bod : t = mk_ ?pos (Let (bs, bod))
let with_ ?pos vs bod : t = mk_ ?pos (With (vs, bod))
let lambda ?pos vs bod : t = mk_ ?pos (Lambda (vs, bod))

let to_string = Fmt.to_string pp

(* TODO *)
let ty_infer _ctx _e : K.Expr.t =
  assert false

