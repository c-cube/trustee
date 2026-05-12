open Sigs
module H = CCHash
module CB = Cbor_pack

module Int_map = CCMap.Make (CCInt)

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

(* ── First mutually-recursive type group ── *)

type ty_or_error =
  | Kind
  | Ty of expr
  | Ill_typed of string

and expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_arrow of expr * expr
  | E_box of sequent

and expr = {
  e_view: expr_view;
  mutable e_ty: ty_or_error;
  mutable e_id: int;
  mutable e_flags: int;
  mutable e_hash: Chash.t;
}

and var = {
  v_name: string;
  v_ty: ty;
}

and ty_var = var

and bvar = {
  bv_idx: int;
  bv_ty: ty;
}

and ty = expr
and expr_set = expr Int_map.t

and sequent = {
  concl: expr;
  hyps: expr_set;
}

and const = {
  c_name: string;
  c_args: const_args;
  c_ty: ty;
  c_concrete: bool;
  c_labels: (string * string) list;
}

and ty_const = const

and const_args =
  | C_ty_vars of ty_var list
  | C_arity of int

(* ── Standalone types ── *)

type const_def =
  | C_def_expr of { vars: ty_var list; rhs: expr }
  | C_def_ty of { arity: int; phi: expr }
  | C_def_ty_abs of { arity: int; phi: expr }
  | C_def_ty_repr of { arity: int; phi: expr }
  | C_def_theory_param of { ty_vars: var list; ty: expr }
  | C_def_theory_ty_param of { arity: int }
  | C_def_skolem of { name: string }
  | C_def_skolem_ty of { name: string; arity: int }
  | C_def_magic of string

type const_kind =
  | C_ty
  | C_term

(* ── Basic inline functions ── *)

let[@inline] expr_eq (e1 : expr) e2 : bool = e1 == e2
let[@inline] expr_hash (e : expr) = H.int e.e_id
let[@inline] expr_compare (e1 : expr) e2 : int = CCInt.compare e1.e_id e2.e_id
let[@inline] expr_db_depth e = e.e_flags lsr (1 + ctx_id_bits)
let[@inline] expr_has_fvars e = (e.e_flags lsr ctx_id_bits) land 1 == 1
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask
let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

let[@inline] sequent_eq s1 s2 =
  expr_eq s1.concl s2.concl && Int_map.equal expr_eq s1.hyps s2.hyps

let[@inline] sequent_hash s =
  H.combine3 193 (expr_hash s.concl)
    (H.iter expr_hash @@ Iter.map snd @@ Int_map.to_iter s.hyps)

let[@inline] const_eq (c1 : const) c2 : bool = String.equal c1.c_name c2.c_name
let const_hash c = H.string c.c_name

(* ── Expr_set ── *)

module Expr_set = struct
  type t = expr_set

  let empty : t = Int_map.empty
  let is_empty = Int_map.is_empty
  let iter k (self : t) = Int_map.iter (fun _ x -> k x) self
  let size = Int_map.cardinal
  let equal = Int_map.equal expr_eq
  let singleton e = Int_map.singleton e.e_id e
  let mem e self = Int_map.mem e.e_id self
  let add e self = Int_map.add e.e_id e self
  let remove e self = Int_map.remove e.e_id self
  let to_list self = Int_map.fold (fun _ x l -> x :: l) self []
  let to_iter (self : t) k = Int_map.iter (fun _ x -> k x) self

  let of_list l : t =
    List.fold_left (fun m e -> Int_map.add e.e_id e m) Int_map.empty l

  let of_iter i : t =
    Iter.fold (fun m e -> Int_map.add e.e_id e m) Int_map.empty i

  let map f self = Int_map.fold (fun _ e acc -> add (f e) acc) self empty

  let union a b : t =
    Int_map.union
      (fun _ e1 e2 ->
        assert (expr_eq e1 e2);
        Some e1)
      a b

  let exists f self =
    try
      Int_map.iter (fun _ e -> if f e then raise_notrace Exit) self;
      false
    with Exit -> true

  let subset a b =
    try
      Int_map.iter
        (fun i _ -> if not (Int_map.mem i b) then raise_notrace Exit)
        a;
      true
    with Exit -> false
end

(* ── Name_k_map ── *)

module Name_k_map = CCMap.Make (struct
  type t = const_kind * string

  let compare (k1, c1) (k2, c2) =
    if k1 = k2 then
      String.compare c1 c2
    else
      Stdlib.compare k1 k2
end)

(* ── Hashcons for expressions ── *)

module Expr_hashcons = Hashcons.Make (struct
  type t = expr

  let equal a b =
    match a.e_view, b.e_view with
    | E_kind, E_kind ->
      (match a.e_ty, b.e_ty with
      | Ill_typed msg1, Ill_typed msg2 -> String.equal msg1 msg2
      | Ill_typed _, _ | _, Ill_typed _ -> false
      | _, _ -> true)
    | E_type, E_type -> true
    | E_const (c1, l1), E_const (c2, l2) ->
      String.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
    | E_var v1, E_var v2 -> var_eq v1 v2
    | E_bound_var v1, E_bound_var v2 ->
      v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
    | E_app (f1, a1), E_app (f2, a2) -> expr_eq f1 f2 && expr_eq a1 a2
    | E_lam (_, ty1, bod1), E_lam (_, ty2, bod2) ->
      expr_eq ty1 ty2 && expr_eq bod1 bod2
    | E_arrow (a1, b1), E_arrow (a2, b2) -> expr_eq a1 a2 && expr_eq b1 b2
    | E_box seq1, E_box seq2 -> sequent_eq seq1 seq2
    | ( ( E_kind | E_type | E_const _ | E_var _ | E_bound_var _ | E_app _
        | E_lam _ | E_arrow _ | E_box _ ),
        _ ) ->
      false

  let hash e : int =
    match e.e_view with
    | E_kind ->
      (match e.e_ty with
      | Ill_typed msg -> H.combine2 99 (H.string msg)
      | _ -> 11)
    | E_type -> 12
    | E_const (c, l) ->
      H.combine4 20 (H.string c.c_name) (expr_hash c.c_ty) (H.list expr_hash l)
    | E_var v -> H.combine2 30 (var_hash v)
    | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
    | E_app (f, a) -> H.combine3 50 (expr_hash f) (expr_hash a)
    | E_box seq -> sequent_hash seq
    | E_lam (_, ty, bod) -> H.combine3 60 (expr_hash ty) (expr_hash bod)
    | E_arrow (a, b) -> H.combine3 80 (expr_hash a) (expr_hash b)

  let set_id t id =
    assert (t.e_id == -1);
    t.e_id <- id

  let on_new e =
    (match e.e_ty with Ty t -> ignore t | _ -> ())
end)

(* ── LRU keyed by string ── *)

module String_LRU = LRU.Make (struct
  type t = string

  let equal = String.equal
  let hash = H.string
end)

(* ── Second mutually-recursive type group ── *)

type thm = {
  th_seq: sequent;
  mutable th_flags: int;
  mutable th_proof: proof;
  mutable th_theory: theory option;
}

and theory = {
  theory_name: string;
  theory_ctx: ctx;
  mutable theory_in_constants: const Name_k_map.t;
  mutable theory_in_theorems: thm list;
  mutable theory_defined_constants: const Name_k_map.t;
  mutable theory_defined_theorems: thm list;
}

and proof =
  | Pr_dummy
  | Pr_main of proof
  | Pr_step of {
      rule: string;
      args: proof_arg list;
      parents: thm list;
    }

and proof_arg =
  | Pr_expr of expr
  | Pr_subst of (var * expr) list

and ctx = {
  ctx_uid: int;
  ctx_exprs: Expr_hashcons.t;
  ctx_kind: expr lazy_t;
  ctx_type: expr lazy_t;
  ctx_bool: expr lazy_t;
  ctx_bool_c: const lazy_t;
  ctx_eq_c: const lazy_t;
  ctx_select_c: const lazy_t;
  ctx_storage: Storage.t;
  ctx_store_concrete_definitions: bool;
  ctx_store_proofs: bool;
  ctx_def_cache: const_def option String_LRU.t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

let[@inline] ctx_check_e_uid ctx (e : expr) =
  assert (ctx.ctx_uid == expr_ctx_uid e)

let[@inline] ctx_check_th_uid ctx (th : thm) =
  assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = "bool"
let id_eq = "="
let id_select = "select"

(* ── unfold_app ── *)

let unfold_app (e : expr) : expr * expr list =
  let rec aux acc e =
    match e.e_view with
    | E_app (f, a) -> aux (a :: acc) f
    | _ -> e, acc
  in
  aux [] e

(* ── Printers ── *)

let __pp_ids = ref false

let pp_seq_ ~pp_expr out seq =
  let { hyps; concl } = seq in
  if Int_map.is_empty hyps then
    Fmt.fprintf out "@[|- %a@]" pp_expr concl
  else
    Fmt.fprintf out "@[<hv>%a@ |- %a@]" (pp_iter pp_expr)
      (Int_map.to_iter hyps |> Iter.map snd)
      pp_expr concl

let rec expr_pp_with_ ~max_depth out (e : expr) : unit =
  let rec loop k ~depth names out e =
    let pp = loop k ~depth:(depth + 1) names in
    let pp' = loop' k ~depth:(depth + 1) names in
    (match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    | E_bound_var v ->
      let idx = v.bv_idx in
      (match CCList.nth_opt names idx with
      | Some n when n <> "" -> Fmt.string out n
      | _ ->
        if idx < k then
          Fmt.fprintf out "x_%d" (k - idx - 1)
        else
          Fmt.fprintf out "%%db_%d" (idx - k))
    | E_const (c, []) -> Fmt.string out c.c_name
    | E_const (c, args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Fmt.string c.c_name
        (pp_list pp') args
    | (E_app _ | E_lam _ | E_arrow _) when depth > max_depth ->
      Fmt.fprintf out "@<1>…/%d" e.e_id
    | E_app _ ->
      let f, args = unfold_app e in
      (match f.e_view, args with
      | E_const (c, [ _ ]), [ a; b ] when String.equal c.c_name "=" ->
        Fmt.fprintf out "@[@[%a@]@ = @[%a@]@]" pp' a pp' b
      | _ -> Fmt.fprintf out "%a@ %a" pp' f (pp_list pp') args)
    | E_box seq -> pp_seq_ ~pp_expr:(loop 0 ~depth:0 []) out seq
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp' _ty
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty
        (loop (k + 1) ~depth:(depth + 1) (n :: names))
        bod
    | E_arrow (a, b) -> Fmt.fprintf out "@[@[%a@]@ -> %a@]" pp' a pp b
    );
    if !__pp_ids then Fmt.fprintf out "/%d" e.e_id
  and loop' k ~depth names out e =
    match e.e_view with
    | E_kind | E_type | E_var _ | E_bound_var _ | E_const (_, []) ->
      loop k ~depth names out e (* atomic expr *)
    | _ -> Fmt.fprintf out "(%a)" (loop k ~depth names) e
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let expr_pp_ = expr_pp_with_ ~max_depth:max_int

(* ── Var, BVar, New_ty_def ── *)

module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let[@inline] map_ty v ~f = { v with v_ty = f v.v_ty }
  let make v_name v_ty : t = { v_name; v_ty }
  let makef fmt ty = Fmt.kasprintf (fun s -> make s ty) fmt
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp

  let pp_with_ty out v =
    Fmt.fprintf out "(@[%s :@ %a@])" v.v_name expr_pp_ v.v_ty

  let to_string = Fmt.to_string pp

  let compare a b : int =
    if expr_eq a.v_ty b.v_ty then
      String.compare a.v_name b.v_name
    else
      expr_compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = t

    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make (AsKey)
  module Set = CCSet.Make (AsKey)
  module Tbl = CCHashtbl.Make (AsKey)
end

module BVar = struct
  type t = bvar

  let make i ty : t = { bv_idx = i; bv_ty = ty }
  let pp out v = Fmt.fprintf out "db_%d" v.bv_idx
  let to_string = Fmt.to_string pp
end

module New_ty_def = struct
  type t = {
    tau: ty_const;
    fvars: var list;
    c_abs: const;
    c_repr: const;
    abs_thm: thm;
    abs_x: var;
    repr_thm: thm;
    repr_x: var;
  }
end

(* ── Subst type ── *)

type subst = {
  ty: expr Var.Map.t;
  m: expr Var.Map.t;
}
