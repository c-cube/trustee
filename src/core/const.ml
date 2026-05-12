open Types
open Sigs

let key_const_def (c_name : string) : string =
  Printf.sprintf "cdef:%s" c_name

module Const_def = struct
  type t = const_def

  let pp out (d : t) =
    let pp_vars = Fmt.Dump.list var_pp in
    match d with
    | C_def_expr { vars; rhs } ->
      Fmt.fprintf out "(@[fun %a.@ %a@])" pp_vars vars expr_pp_ rhs
    | C_def_ty { arity; phi } ->
      Fmt.fprintf out "(@[def-ty/%d@ %a@])" arity expr_pp_ phi
    | C_def_ty_abs { arity; phi } ->
      Fmt.fprintf out "(@[def-ty-abs/%d@ %a@])" arity expr_pp_ phi
    | C_def_ty_repr { arity; phi } ->
      Fmt.fprintf out "(@[def-ty-repr/%d@ %a@])" arity expr_pp_ phi
    | C_def_theory_param { ty_vars; ty } ->
      Fmt.fprintf out "(@[def-theory-param@ %a@ %a@])" pp_vars ty_vars expr_pp_
        ty
    | C_def_theory_ty_param { arity } ->
      Fmt.fprintf out "(@[def-theory-ty-param/%d@])" arity
    | C_def_skolem { name } -> Fmt.fprintf out "(@[skolem %S@])" name
    | C_def_skolem_ty { name; arity } ->
      Fmt.fprintf out "(@[skolem-ty/%d %S@])" arity name
    | C_def_magic ma -> Fmt.fprintf out "(magic %S)" ma

  let to_string = Fmt.to_string pp
  let enc = Expr.Util_enc_.enc_const_def
  let dec = Expr.Util_dec_.dec_const_def

  let map ~f (def : t) : t =
    match def with
    | C_def_expr { vars; rhs } ->
      let vars = List.map (fun v -> { v with v_ty = f v.v_ty }) vars in
      C_def_expr { vars; rhs = f rhs }
    | C_def_ty { arity; phi } -> C_def_ty { arity; phi = f phi }
    | C_def_ty_abs { arity; phi } -> C_def_ty_abs { arity; phi = f phi }
    | C_def_ty_repr { arity; phi } -> C_def_ty_repr { arity; phi = f phi }
    | C_def_theory_param { ty_vars; ty } ->
      C_def_theory_param { ty_vars; ty = f ty }
    | C_def_theory_ty_param _ | C_def_skolem_ty _ | C_def_magic _
    | C_def_skolem _ ->
      def

  let approx_def = function
    | C_def_expr { rhs } -> `Def rhs
    | C_def_ty { phi } -> `Ty_def phi
    | C_def_theory_ty_param _ | C_def_theory_param _ -> `Param
    | _ -> `Other
end

type t = const
type def = const_def

type args = const_args =
  | C_ty_vars of ty_var list
  | C_arity of int

let[@inline] pp out c = Fmt.string out c.c_name
let[@inline] pp_cname out c = Fmt.string out c.c_name
let[@inline] to_string c = Fmt.to_string pp c
let[@inline] cname c = c.c_name
let[@inline] name c = c.c_name
let[@inline] equal c1 c2 = String.equal c1.c_name c2.c_name
let[@inline] args c = c.c_args
let[@inline] ty c = c.c_ty
let[@inline] labels c = c.c_labels

let chash (self : t) : Chash.t =
  Chash.run Chash.string self.c_name

let pp_with_ty out c =
  Fmt.fprintf out "`@[%a@ : %a@]`" Fmt.string c.c_name expr_pp_ c.c_ty

let enc = Expr.Util_enc_.enc_const
let dec = Expr.Util_dec_.dec_const
let[@inline] eq ctx = Lazy.force ctx.ctx_eq_c
let[@inline] bool ctx = Lazy.force ctx.ctx_bool_c
let[@inline] select ctx = Lazy.force ctx.ctx_select_c

let pp_args out = function
  | C_arity 0 -> ()
  | C_arity n -> Fmt.fprintf out "/%d" n
  | C_ty_vars [] -> ()
  | C_ty_vars vs -> Fmt.fprintf out " %a" (Fmt.Dump.list var_pp) vs

let expr_is_concrete_ (e : expr) : bool =
  try
    Expr.iter_dag ~iter_ty:true e ~f:(fun e ->
        match e.e_view with
        | E_const (c, _) -> if not c.c_concrete then raise Exit
        | _ -> ());
    true
  with Exit -> false

let is_concrete_def (def : const_def) : bool =
  match def with
  | C_def_expr { rhs = e }
  | C_def_ty { phi = e }
  | C_def_ty_abs { phi = e }
  | C_def_ty_repr { phi = e } ->
    expr_is_concrete_ e
  | C_def_theory_param _ | C_def_theory_ty_param _ | C_def_skolem _
  | C_def_skolem_ty _ | C_def_magic _ ->
    false

let cname_bool = id_bool
let cname_eq = id_eq
let cname_select = id_select

let make (ctx : ctx) ~def ?(labels = []) name args ty : t =
  let is_concrete = is_concrete_def def in
  if ctx.ctx_store_concrete_definitions || not is_concrete then
    Storage.store ctx.ctx_storage ~erase:false ~key:(key_const_def name)
      Const_def.enc def;
  { c_name = name; c_concrete = is_concrete; c_ty = ty; c_args = args; c_labels = labels }

let get_def (self : ctx) (c : t) : const_def option =
  String_LRU.get self.ctx_def_cache c.c_name ~compute:(fun _ ->
      let key = key_const_def c.c_name in
      Storage.get self.ctx_storage (Const_def.dec self) ~key)

let get_def_exn self c =
  match get_def self c with
  | Some d -> d
  | None ->
    Error.failf (fun k -> k "cannot find definition for %s" c.c_name)

let new_const ctx name ty_vars ty ~def : t =
  let fvars = Expr.free_vars ty in
  let diff = Var.Set.diff fvars (Var.Set.of_list ty_vars) in
  (match Var.Set.choose_opt diff with
  | None -> ()
  | Some v ->
    Error.failf (fun k ->
        k
          "Kernel.new_const: type variable %a@ occurs in type of the \
           constant `%s`,@ but not in the type variables %a"
          Var.pp v name (Fmt.Dump.list Var.pp) ty_vars));
  make ctx ~def name (C_ty_vars ty_vars) ty

let new_ty_const ctx name n ~def : ty_const =
  make ctx ~def name (C_arity n) (Expr.type_ ctx)
