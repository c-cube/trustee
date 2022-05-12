
(** {1 Kernel of trust} *)

open Sigs
module H = CCHash
module CB = Cbor_pack

(* NOTE: this seems slightly faster than Patricia trees,
   if run on opentheory *)
module Int_map = CCMap.Make(CCInt)

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_arrow of expr * expr
  | E_box of sequent (* reified sequent *)

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* contains: [higher DB var | 1:has free vars | 5:ctx uid] *)
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
  c_name : Cname.t;
  c_args: const_args;
  c_ty: ty; (* free vars are [vs] if [c_args = C_ty_vars vs] *)
  c_concrete: bool; (* if true, def can be erased *) (* TODO *)
}
and ty_const = const

and const_args =
  | C_ty_vars of ty_var list
  | C_arity of int (* for type constants *)

type const_def =
  | C_def_expr of {vars: ty_var list; rhs: expr}
  | C_def_ty of {arity: int; phi: expr}
  | C_def_ty_abs of {arity: int; phi: expr}
  | C_def_ty_repr of {arity: int; phi: expr}
  | C_def_theory_param of {ty_vars: var list; ty: expr}
  | C_def_theory_ty_param of {arity: int}
  | C_def_skolem of {name: string}
  | C_def_skolem_ty of {name: string; arity: int}
  | C_def_magic of string

let[@inline] expr_eq (e1:expr) e2 : bool = e1 == e2
let[@inline] expr_hash (e:expr) = H.int e.e_id
let[@inline] expr_compare (e1:expr) e2 : int = CCInt.compare e1.e_id e2.e_id
let[@inline] expr_db_depth e = e.e_flags lsr (1+ctx_id_bits)
let[@inline] expr_has_fvars e = ((e.e_flags lsr ctx_id_bits) land 1) == 1
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask

let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

let[@inline] sequent_eq s1 s2 =
  expr_eq s1.concl s2.concl &&
  Int_map.equal expr_eq s1.hyps s2.hyps
let[@inline] sequent_hash s =
  H.combine3 193 (expr_hash s.concl)
    (H.iter expr_hash @@ Iter.map snd @@ Int_map.to_iter s.hyps)

let[@inline] const_eq (c1:const) c2 : bool =
  Cname.equal c1.c_name c2.c_name

let const_hash c = Cname.hash c.c_name

module Expr_set = struct
  type t = expr_set
  let empty : t = Int_map.empty
  let is_empty = Int_map.is_empty
  let iter k (self:t) = Int_map.iter (fun _ x -> k x) self
  let size = Int_map.cardinal
  let equal = Int_map.equal expr_eq
  let singleton e = Int_map.singleton e.e_id e
  let mem e self = Int_map.mem e.e_id self
  let add e self = Int_map.add e.e_id e self
  let remove e self = Int_map.remove e.e_id self
  let to_list self = Int_map.fold (fun _ x l -> x :: l) self []
  let to_iter (self:t) k = Int_map.iter (fun _ x -> k x) self
  let of_list l : t =
    List.fold_left (fun m e -> Int_map.add e.e_id e m) Int_map.empty l
  let of_iter i : t =
    Iter.fold (fun m e -> Int_map.add e.e_id e m) Int_map.empty i
  let map f self =
    Int_map.fold
      (fun _ e acc -> add (f e) acc)
      self empty
  let union a b : t =
    Int_map.union (fun _ e1 e2 -> assert (expr_eq e1 e2); Some e1) a b
  let exists f self =
    try
      Int_map.iter (fun _ e -> if f e then raise_notrace Exit) self; false
    with Exit -> true
  let subset a b =
    try
      Int_map.iter (fun i _ -> if not (Int_map.mem i b) then raise_notrace Exit) a;
      true
    with Exit -> false
end

(* open an application *)
let unfold_app (e:expr) : expr * expr list =
  let rec aux acc e =
    match e.e_view with
    | E_app (f, a) -> aux (a::acc) f
    | _ -> e, acc
  in
  aux [] e

let __pp_ids = ref false

let pp_seq_ ~pp_expr out seq =
  let {hyps; concl} = seq in
  if Int_map.is_empty hyps then (
    Fmt.fprintf out "@[|- %a@]" pp_expr concl
  ) else (
    Fmt.fprintf out "@[<hv>%a@ |- %a@]"
      (pp_iter pp_expr) (Int_map.to_iter hyps |> Iter.map snd)
      pp_expr concl
  )

(* debug printer *)
let expr_pp_with_ ~max_depth out (e:expr) : unit =
  let rec loop k ~depth names out e =
    let pp = loop k ~depth:(depth+1) names in
    let pp' = loop' k ~depth:(depth+1) names in
    (match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
    | E_bound_var v ->
      let idx = v.bv_idx in
      begin match CCList.nth_opt names idx with
        | Some n when n<>"" -> Fmt.string out n
        | _ ->
          if idx<k then Fmt.fprintf out "x_%d" (k-idx-1)
          else Fmt.fprintf out "%%db_%d" (idx-k)
      end
    | E_const (c,[]) -> Fmt.string out (Cname.name c.c_name)
    | E_const (c,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Fmt.string (Cname.name c.c_name) (pp_list pp') args
    | (E_app _ | E_lam _ | E_arrow _) when depth > max_depth ->
      Fmt.fprintf out "@<1>…/%d" e.e_id
    | E_app _ ->
      let f, args = unfold_app e in
      begin match f.e_view, args with
        | E_const (c, [_]), [a;b] when String.equal (Cname.name c.c_name) "=" ->
          Fmt.fprintf out "@[@[%a@]@ = @[%a@]@]" pp' a pp' b
        | _ ->
          Fmt.fprintf out "%a@ %a" pp' f (pp_list pp') args
      end
    | E_box seq ->
      pp_seq_ ~pp_expr:(loop 0 ~depth:0 []) out seq
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp' _ty
        (loop (k+1) ~depth:(depth+1) (""::names)) bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty
        (loop (k+1) ~depth:(depth+1) (n::names)) bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[@[%a@]@ -> %a@]" pp' a pp b
    );
    if !__pp_ids then Fmt.fprintf out "/%d" e.e_id;

  and loop' k ~depth names out e = match e.e_view with
    | E_kind | E_type | E_var _ | E_bound_var _ | E_const (_, []) ->
      loop k ~depth names out e (* atomic expr *)
    | _ -> Fmt.fprintf out "(%a)" (loop k ~depth names) e
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let expr_pp_ = expr_pp_with_ ~max_depth:max_int

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const (c1,l1), E_const (c2,l2) ->
          Cname.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_bound_var v1, E_bound_var v2 ->
          v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (_,ty1,bod1), E_lam (_,ty2,bod2) ->
          expr_eq ty1 ty2 && expr_eq bod1 bod2
        | E_arrow(a1,b1), E_arrow(a2,b2) ->
          expr_eq a1 a2 && expr_eq b1 b2
        | E_box seq1, E_box seq2 ->
          sequent_eq seq1 seq2
        | (E_kind | E_type | E_const _ | E_var _ | E_bound_var _
          | E_app _ | E_lam _ | E_arrow _ | E_box _), _ -> false
      end

    let hash e : int =
      match e.e_view with
      | E_kind -> 11
      | E_type -> 12
      | E_const (c,l) ->
        H.combine4 20 (Cname.hash c.c_name) (expr_hash c.c_ty) (H.list expr_hash l)
      | E_var v -> H.combine2 30 (var_hash v)
      | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
      | E_app (f,a) -> H.combine3 50 (expr_hash f) (expr_hash a)
      | E_box seq -> sequent_hash seq
      | E_lam (_,ty,bod) ->
        H.combine3 60 (expr_hash ty) (expr_hash bod)
      | E_arrow (a,b) -> H.combine3 80 (expr_hash a) (expr_hash b)

    let set_id t id =
      assert (t.e_id == -1);
      t.e_id <- id

    let on_new e = ignore (Lazy.force e.e_ty : _ option)
    end)

type const_kind = C_ty | C_term

(* special map for indexing constants, differentiating type and term constants *)
module Name_k_map = CCMap.Make(struct
    type t = const_kind * string
    let compare (k1,c1)(k2,c2) =
      if k1=k2 then String.compare c1 c2 else Stdlib.compare k1 k2
  end)

type thm = {
  th_seq: sequent;
  mutable th_flags: int; (* [bool flags|ctx uid] *)
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
  ctx_select_c : const lazy_t;
  ctx_storage: Storage.t;
  ctx_store_concrete_definitions: bool;
  ctx_store_proofs: bool;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = "bool"
let id_eq = "="
let id_select = "select"

module Expr0 = struct
  type t = expr

  let[@inline] ty e = Lazy.force e.e_ty
  let[@inline] view e = e.e_view
  let[@inline] ty_exn e = match e.e_ty with
    | lazy None -> assert false
    | lazy (Some ty) -> ty

  let equal = expr_eq
  let hash = expr_hash

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)

  let iter ~f (e:expr) : unit =
    match e.e_view with
    | E_kind | E_type -> ()
    | _ ->
      begin match e.e_ty with
        | lazy None -> assert false
        | lazy (Some ty) -> f false ty
      end;
      match e.e_view with
      | E_box _ | E_const _ -> ()
      | E_kind | E_type -> assert false
      | E_var v -> f false v.v_ty
      | E_bound_var v -> f false v.bv_ty
      | E_app (hd,a) -> f false hd; f false a
      | E_lam (_, tyv, bod) -> f false tyv; f true bod
      | E_arrow (a,b) -> f false a; f false b

  let iter_dag ~iter_ty ~f e : unit =
    let tbl = Tbl.create 8 in
    let rec loop e =
      if not (Tbl.mem tbl e) then (
        Tbl.add tbl e ();
        if iter_ty then Option.iter loop (Lazy.force e.e_ty);
        f e;
        iter e ~f:(fun _ u -> loop u)
      )
    in
    loop e

  let iter_dag' ~iter_ty e f = iter_dag ~iter_ty ~f e

  (* forward declaration *)
  let make_expr_ = ref (fun _ _ _ -> assert false)
end

module Util_chash_ = struct
  module H = Chash

  let rec hash_expr_ (e:expr) : H.t =
    let compute_ e =
      (* compute hash pf [e] *)
      let ctx = H.create() in
      begin match Lazy.force e.e_ty with
        | Some ty -> hasher_expr_ ctx ty
        | None -> ()
      end;
      begin match e.e_view with
        | E_var v ->
          H.string ctx "v"; H.string ctx v.v_name
        | E_const (c,args) ->
          H.string ctx "c";
          Cname.chasher ctx c.c_name;  (* need to use name+hash *)
          List.iter (hasher_expr_ ctx) args
        | E_bound_var v ->
          H.string ctx "b"; H.int ctx v.bv_idx
        | E_app (hd,a) ->
          H.string ctx "@"; hasher_expr_ ctx hd; hasher_expr_ ctx a
        | E_lam (n, tyv, bod) ->
          H.string ctx "l"; hasher_expr_ ctx bod
        | E_arrow (a,b) ->
          H.string ctx ">"
        | E_kind -> H.string ctx "K"
        | E_type -> H.string ctx "T"
        | E_box seq ->
          H.string ctx "["; hasher_seq_ ctx seq
      end;
      H.finalize ctx
    in

    (* is hash computed already? *)
    if Chash.equal Chash.dummy e.e_hash then (
      let h = compute_ e in
      e.e_hash <- h;
      h
    ) else (
      e.e_hash (* in cache *)
    )

  (* add hash of [e] to [ctx] *)
  and[@inline] hasher_expr_ ctx e =
    let h = hash_expr_ e in
    H.sub ctx h

  (* add hash of [s] to [ctx] *)
  and hasher_seq_ ctx (s:sequent) : unit =
    let l =
      List.rev_map hash_expr_ (Expr_set.to_list s.hyps)
      |> List.sort Chash.compare
    in
    H.string ctx "seq";
    List.iter (H.sub ctx) l;
    H.string ctx "|-";
    H.sub ctx (hash_expr_ s.concl)

  let hasher_const_def_ ctx (d:const_def) =
    match d with
    | C_def_expr {vars; rhs} ->
      H.string ctx "def";
      List.iter (fun v -> H.string ctx v.v_name; hasher_expr_ ctx v.v_ty) vars;
      H.sub ctx (hash_expr_ rhs)
    | C_def_ty {arity; phi} ->
      H.string ctx "ty"; H.int ctx arity; H.sub ctx (hash_expr_ phi)
    | C_def_ty_abs {arity; phi} ->
      H.string ctx "ty.abs"; H.int ctx arity; H.sub ctx (hash_expr_ phi)
    | C_def_ty_repr {arity; phi} ->
      H.string ctx "ty.repr"; H.int ctx arity; H.sub ctx (hash_expr_ phi)
    | C_def_theory_param {ty_vars; ty} ->
      H.string ctx "param";
      List.iter (fun v -> H.string ctx v.v_name) ty_vars;
      H.sub ctx (hash_expr_ ty)
    | C_def_theory_ty_param {arity} ->
      H.string ctx "ty.param"; H.int ctx arity
    | C_def_magic magic ->
      H.string ctx "magic"; H.string ctx magic
    | C_def_skolem {name} ->
      H.string ctx "sk.e"; H.string ctx name
    | C_def_skolem_ty {name;arity} ->
      H.string ctx "sk.ty"; H.string ctx name

  let hash_const_def_ ~name (d:const_def) : H.t =
    let ctx = H.create() in
    H.string ctx name;
    hasher_const_def_ ctx d;
    H.finalize ctx
end

(** Storage key for a constant definition *)
let key_const_def (c_name:Cname.t) : string =
  Printf.sprintf "cdef:%s:%s" c_name.name (Chash.to_string c_name.chash)

module Const_def = struct
  type t = const_def

  let pp out (d:t) =
    let pp_vars = Fmt.Dump.list var_pp in
    match d with
    | C_def_expr {vars;rhs} ->
      Fmt.fprintf out "(@[fun %a.@ %a@])"
        pp_vars vars expr_pp_ rhs
    | C_def_ty {arity; phi} ->
      Fmt.fprintf out "(@[def-ty/%d@ %a@])" arity expr_pp_ phi
    | C_def_ty_abs {arity; phi} ->
      Fmt.fprintf out "(@[def-ty-abs/%d@ %a@])" arity expr_pp_ phi
    | C_def_ty_repr {arity; phi} ->
      Fmt.fprintf out "(@[def-ty-repr/%d@ %a@])" arity expr_pp_ phi
    | C_def_theory_param { ty_vars; ty } ->
      Fmt.fprintf out "(@[def-theory-param@ %a@ %a@])"
        pp_vars ty_vars expr_pp_ ty
    | C_def_theory_ty_param { arity } ->
      Fmt.fprintf out "(@[def-theory-ty-param/%d@])" arity
    | C_def_skolem { name } -> Fmt.fprintf out "(@[skolem %S@])" name
    | C_def_skolem_ty { name; arity } ->
      Fmt.fprintf out "(@[skolem-ty/%d %S@])" arity name
    | C_def_magic ma -> Fmt.fprintf out "(magic %S)" ma

  let to_string = Fmt.to_string pp

  let enc _ _ = assert false (* TODO *)

  let dec _ =
    let open CB.Dec in
    return (C_def_magic "") (* FIXME *)

  let map ~f (def:t) : t =
    match def with
    | C_def_expr {vars;rhs} ->
      let vars = List.map (fun v -> {v with v_ty=f v.v_ty}) vars in
      C_def_expr {vars;rhs=f rhs}
    | C_def_ty {arity;phi} -> C_def_ty {arity;phi=f phi}
    | C_def_ty_abs {arity;phi}-> C_def_ty_abs {arity;phi=f phi}
    | C_def_ty_repr {arity;phi}-> C_def_ty_repr {arity;phi=f phi}
    | C_def_theory_param {ty_vars;ty} -> C_def_theory_param {ty_vars;ty=f ty}
    | C_def_theory_ty_param _ | C_def_skolem_ty _
    | C_def_magic _ | C_def_skolem _ -> def

  let approx_def = function
    | C_def_expr {rhs} -> `Def rhs
    | C_def_ty {phi} -> `Ty_def phi
    | C_def_theory_ty_param _ | C_def_theory_param _ -> `Param
    | _ -> `Other
end

module Const = struct
  type t = const
  type def = const_def
  type args = const_args =
    | C_ty_vars of ty_var list
    | C_arity of int

  let[@inline] pp out c = Fmt.string out (Cname.name c.c_name)
  let[@inline] to_string c = Fmt.to_string pp c
  let[@inline] cname c = c.c_name
  let[@inline] name c = c.c_name.name
  let[@inline] equal c1 c2 = Cname.equal c1.c_name c2.c_name
  let[@inline] args c = c.c_args
  let[@inline] ty c = c.c_ty

  (* obtain the hash *)
  let chash (self:t) : Chash.t =
    let h = Cname.chash self.c_name in
    assert (not (Chash.equal h Chash.dummy));
    h

  let pp_with_ty out c =
    Fmt.fprintf out "`@[%a@ : %a@]`"
      Cname.pp_name c.c_name expr_pp_ c.c_ty

  let[@inline] eq ctx = Lazy.force ctx.ctx_eq_c
  let[@inline] bool ctx = Lazy.force ctx.ctx_bool_c
  let[@inline] select ctx = Lazy.force ctx.ctx_select_c

  let pp_args out = function
    | C_arity 0 -> ()
    | C_arity n -> Fmt.fprintf out "/%d" n
    | C_ty_vars [] -> ()
    | C_ty_vars vs -> Fmt.fprintf out " %a" (Fmt.Dump.list var_pp) vs

  let[@inline] args c = c.c_args

  let expr_is_concrete_ (e:expr) : bool =
    try
      Expr0.iter_dag ~iter_ty:true e
        ~f:(fun e ->
            match e.e_view with
            | E_const (c,_) -> if not c.c_concrete then raise Exit
            | _ -> ());
      true
    with Exit -> false

  let is_concrete_def (def:const_def) : bool =
    match def with
    | C_def_expr {rhs=e}
    | C_def_ty {phi=e}
    | C_def_ty_abs {phi=e}
    | C_def_ty_repr {phi=e} -> expr_is_concrete_ e

    | C_def_theory_param _ | C_def_theory_ty_param _
    | C_def_skolem _ | C_def_skolem_ty _
    | C_def_magic _ -> false

  (* used to compute some cnames independently of a ctx *)
  let cname_of_def ~name ~def : Cname.t =
    let chash = Util_chash_.hash_const_def_ ~name def in
    Cname.make name chash

  let cname_magic_ name = cname_of_def ~name ~def:(C_def_magic name)
  let cname_bool = cname_magic_ id_bool
  let cname_eq = cname_magic_ id_eq
  let cname_select = cname_magic_ id_select

  (* make a constant *)
  let make (ctx:ctx) ~def ?chash name args ty : t =
    (* hash name+definition, since equality on (name,def)
       is the definition of equality for constants. *)
    let chash = match chash with
      | Some h -> h
      | None -> Util_chash_.hash_const_def_ ~name def
    in
    let c_name = Cname.make name chash in
    let is_concrete = is_concrete_def def in
    if ctx.ctx_store_concrete_definitions || not is_concrete then (
      Storage.store ctx.ctx_storage ~key:(key_const_def c_name)
        Const_def.enc def;
    );
    { c_name; c_concrete=is_concrete; c_ty=ty; c_args=args; }

  let get_def (self:ctx) (c:t) : const_def option =
    let cname = c.c_name in
    let key = key_const_def cname in
    Storage.get self.ctx_storage (Const_def.dec self) ~key

  let get_def_exn self c = match get_def self c with
    | Some d -> d
    | None ->
      Error.failf
        (fun k->k"cannot find definition for %a" Cname.pp c.c_name)
end

module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let[@inline] map_ty v ~f = {v with v_ty=f v.v_ty}
  let make v_name v_ty : t = {v_name; v_ty}
  let makef fmt ty = Fmt.kasprintf (fun s->make s ty) fmt
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp
  let pp_with_ty out v =
    Fmt.fprintf out "(@[%s :@ %a@])" v.v_name expr_pp_ v.v_ty
  let to_string = Fmt.to_string pp
  let compare a b : int =
    if expr_eq a.v_ty b.v_ty
    then String.compare a.v_name b.v_name
    else expr_compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)
end

type subst = {
  ty: expr Var.Map.t; (* ty subst *)
  m: expr Var.Map.t; (* term subst *)
}

module BVar = struct
  type t = bvar
  let make i ty : t = {bv_idx=i; bv_ty=ty}
  let pp out v = Fmt.fprintf out "db_%d" v.bv_idx
  let to_string = Fmt.to_string pp
end

module Expr = struct
  include Expr0

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * expr list
    | E_app of t * t
    | E_lam of string * t * t
    | E_arrow of t * t
    | E_box of sequent

  let pp = expr_pp_
  let to_string = Fmt.to_string pp
  let pp_depth = expr_pp_with_

  let compare = expr_compare
  let db_depth = expr_db_depth
  let has_fvars = expr_has_fvars

  type 'a with_ctx = ctx -> 'a

  let chash = Util_chash_.hash_expr_

  exception E_exit

  let[@inline] exists ~f e : bool =
    try
      iter e ~f:(fun b x -> if f b x then raise_notrace E_exit); false
    with E_exit -> true

  let[@inline] for_all ~f e : bool =
    try
      iter e ~f:(fun b x -> if not (f b x) then raise_notrace E_exit); true
    with E_exit -> false

  let[@inline] is_closed e : bool = db_depth e == 0

  let compute_db_depth_ e : int =
    let d1 = match ty e with
      | None -> 0
      | Some d -> db_depth d
    in
    let d2 = match view e with
      | E_kind | E_type | E_const _ | E_var _ | E_box _ -> 0
      | E_bound_var v -> v.bv_idx+1
      | E_app (a,b) | E_arrow (a,b) -> max (db_depth a) (db_depth b)
      | E_lam (_, ty,bod) ->
        max (db_depth ty) (max 0 (db_depth bod - 1))
    in
    max d1 d2

  let compute_has_fvars_ e : bool =
    begin match ty e with
      | None -> false
      | Some ty -> has_fvars ty
    end ||
    begin match view e with
      | E_var _ -> true
      | E_box _ | E_kind | E_type | E_bound_var _ -> false
      | E_const (_, args) -> List.exists has_fvars args
      | E_app (a,b) | E_arrow (a,b) -> has_fvars a || has_fvars b
      | E_lam (_,ty,bod) -> has_fvars ty || has_fvars bod
    end

  (* hashconsing + computing metadata *)
  let make_ (ctx:ctx) view ty : t =
    let e = { e_view=view; e_ty=ty; e_id= -1; e_flags=0; e_hash=Chash.dummy } in
    let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
    if e == e_h then (
      (* new term, compute metadata *)
      assert ((ctx.ctx_uid land ctx_id_mask) == ctx.ctx_uid);
      let has_fvars = compute_has_fvars_ e in
      e_h.e_flags <-
        ((compute_db_depth_ e) lsl (1+ctx_id_bits))
        lor (if has_fvars then 1 lsl ctx_id_bits else 0)
        lor ctx.ctx_uid;
      ctx_check_e_uid ctx e_h;
    );
    e_h

  let () = Expr0.make_expr_ := make_

  let kind ctx = Lazy.force ctx.ctx_kind
  let type_ ctx = Lazy.force ctx.ctx_type

  let[@inline] is_eq_to_type e = match view e with | E_type -> true | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty_exn e)
  let is_eq_to_bool e =
    match view e with E_const (c,[]) -> Cname.equal c.c_name Const.cname_bool | _ -> false
  let[@inline] is_a_bool e = is_eq_to_bool (ty_exn e)
  let[@inline] is_arrow e = match view e with E_arrow _ -> true | _ -> false
  let[@inline] is_lam e = match view e with E_lam _ -> true | _ -> false

  let bool ctx = Lazy.force ctx.ctx_bool

  let var ctx v : t =
    ctx_check_e_uid ctx v.v_ty;
    make_ ctx (E_var v) (Lazy.from_val (Some v.v_ty))

  let var_name ctx s ty : t = var ctx {v_name=s; v_ty=ty}

  let bvar ctx i ty : t =
    assert (i>=0);
    ctx_check_e_uid ctx ty;
    make_ ctx (E_bound_var {bv_idx=i; bv_ty=ty}) (Lazy.from_val (Some ty))

  (* map immediate subterms *)
  let[@inline] map ctx ~f (e:t) : t =
    match view e with
    | E_kind | E_type | E_const (_,[]) | E_box _ -> e
    | _ ->
      let ty' = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (f false ty)
      ) in
      begin match view e with
        | E_var v ->
          let v_ty = f false v.v_ty in
          if v_ty == v.v_ty then e
          else make_ ctx (E_var {v with v_ty}) ty'
        | E_const (c,args) ->
          let args' = List.map (f false) args in
          if List.for_all2 equal args args'
          then e
          else make_ ctx (E_const (c,args')) ty'
        | E_bound_var v ->
          let ty' = f false v.bv_ty in
          if v.bv_ty == ty' then e
          else make_ ctx (E_bound_var {v with bv_ty=ty'}) (Lazy.from_val (Some ty'))
        | E_app (hd,a) ->
          let hd' =  f false hd in
          let a' =  f false a in
          if a==a' && hd==hd' then e
          else make_ ctx (E_app (f false hd, f false a)) ty'
        | E_lam (n, tyv, bod) ->
          let tyv' = f false tyv in
          let bod' = f true bod in
          if tyv==tyv' && bod==bod' then e
          else make_ ctx (E_lam (n, tyv', bod')) ty'
        | E_arrow (a,b) ->
          let a' = f false a in
          let b' = f false b in
          if a==a' && b==b' then e
          else make_ ctx (E_arrow (a', b')) ty'
        | E_kind | E_type | E_box _ -> assert false
      end

  exception IsSub

  let contains e ~sub : bool =
    let rec aux e =
      if equal e sub then raise_notrace IsSub;
      iter e ~f:(fun _ u -> aux u)
    in
    try aux e; false with IsSub -> true

  let free_vars_iter e : var Iter.t =
    fun yield ->
      let rec aux e =
        match view e with
        | E_var v -> yield v; aux (Var.ty v)
        | E_const (_, args) -> List.iter aux args
        | _ -> iter e ~f:(fun _ u -> aux u)
      in
      aux e

  let free_vars ?(init=Var.Set.empty) e : Var.Set.t =
    let set = ref init in
    free_vars_iter e (fun v -> set := Var.Set.add v !set);
    !set

  let id_gen_ = ref 0 (* note: updated atomically *)

  let new_const ctx name ty_vars ty ~def : const =
    let fvars = free_vars ty in
    let diff = Var.Set.diff fvars (Var.Set.of_list ty_vars) in
    begin match Var.Set.choose_opt diff with
      | None -> ()
      | Some v ->
        Error.failf
          (fun k->k
              "Kernel.new_const: type variable %a@ \
               occurs in type of the constant `%s`,@ \
               but not in the type variables %a"
              Var.pp v name (Fmt.Dump.list Var.pp) ty_vars);
    end;
    Const.make ctx ~def name (C_ty_vars ty_vars) ty

  let new_ty_const ctx name n ~def : ty_const =
    Const.make ctx ~def name (C_arity n) (type_ ctx)

  let mk_const_ ctx c args ty : t =
    make_ ctx (E_const (c,args)) ty

  let subst_empty_ : subst =
    {ty=Var.Map.empty;
     m=Var.Map.empty;
    }

  let subst_pp_ out (self:subst) : unit =
    if Var.Map.is_empty self.m && Var.Map.is_empty self.ty then (
      Fmt.string out "{}"
    ) else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp_with_ty v expr_pp_ t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_iter ~sep:" " pp_b)
        (Iter.append (Var.Map.to_iter self.ty) (Var.Map.to_iter self.m))
    )

  (* Bind a variable into a substitution. *)
  let subst_bind_ (subst:subst) v t : subst =
    if is_eq_to_type v.v_ty then (
      { subst with ty=Var.Map.add v t subst.ty }
    ) else (
      { subst with m=Var.Map.add v t subst.m;  }
    )

  let db_shift ctx (e:t) (n:int) =
    ctx_check_e_uid ctx e;
    assert (Option.for_all is_closed (Lazy.force e.e_ty));
    let rec loop e k : t =
      if is_closed e then e
      else if is_a_type e then e
      else (
        match view e with
        | E_bound_var bv ->
          if bv.bv_idx >= k
          then bvar ctx (bv.bv_idx + n) bv.bv_ty
          else bvar ctx bv.bv_idx bv.bv_ty
        | _ ->
          map ctx e ~f:(fun inbind u -> loop u (if inbind then k+1 else k))
      )
    in
    assert (n >= 0);
    if n = 0 then e else loop e 0

  module E_int_tbl = CCHashtbl.Make(struct
      type t = expr * int
      let equal (t1,k1) (t2,k2) = equal t1 t2 && k1==k2
      let hash (t,k) = H.combine3 27 (hash t) (H.int k)
    end)

  let subst_ ctx ~recursive e0 (subst:subst) : t =
    (* cache for types and some terms *)
    let cache_ = E_int_tbl.create 16 in
    let ty_subst_empty_ = Var.Map.is_empty subst.ty in

    let rec loop k e =
      if is_a_type e then (
        (* type subst: can use a cache, and only consider subst.ty
           with k=0 since there are no binders *)
        if ty_subst_empty_ then e
        else (
          try E_int_tbl.find cache_ (e,0)
          with Not_found ->
            let r = loop_uncached_ 0 e in
            E_int_tbl.add cache_ (e,0) r;
            r
        )
      ) else (
        try E_int_tbl.find cache_ (e,k)
        with Not_found ->
          let r = loop_uncached_ k e in
          E_int_tbl.add cache_ (e,k) r;
          r
      )

    and loop_uncached_ k (e:t) : t =
      match view e with
      | _ when not (has_fvars e) -> e (* nothing to subst in *)
      | E_var v when is_eq_to_type v.v_ty ->
        (* type variable substitution *)
        begin match Var.Map.find v subst.ty with
          | u ->
            assert (is_closed u); if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_var v ->
        (* first, subst in type *)
        let v = {v with v_ty=loop k v.v_ty} in
        begin match Var.Map.find v subst.m with
          | u ->
            let u = db_shift ctx u k in
            if recursive then loop 0 u else u
          | exception Not_found -> var ctx v
        end
      | E_const (_, []) -> e
      | _ ->
        map ctx e ~f:(fun inb u -> loop (if inb then k+1 else k) u)
    in

    if Var.Map.is_empty subst.m && Var.Map.is_empty subst.ty then (
      e0
    ) else (
      loop 0 e0
    )

  let[@inline] subst ctx ~recursive e subst =
    subst_ ctx ~recursive e subst

  let const ctx c args : t =
    ctx_check_e_uid ctx c.c_ty;
    let ty =
      match c.c_args with
      | C_arity n ->
        if List.length args <> n then (
          Error.failf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                Cname.pp_name c.c_name
                n (List.length args));
        );
        Lazy.from_val (Some c.c_ty)
      | C_ty_vars ty_vars ->
        if List.length args <> List.length ty_vars then (
          Error.failf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                Cname.pp_name c.c_name
                (List.length ty_vars) (List.length args));
        );
        lazy (
          let sigma = List.fold_left2 subst_bind_ subst_empty_ ty_vars args in
          Some (subst ~recursive:false ctx c.c_ty sigma)
        )
    in
    mk_const_ ctx c args ty

  let eq ctx ty =
    let eq = Lazy.force ctx.ctx_eq_c in
    const ctx eq [ty]

  let select ctx ty =
    let sel = Lazy.force ctx.ctx_select_c in
    const ctx sel [ty]

  let abs_on_ ctx (v:var) (e:t) : t =
    ctx_check_e_uid ctx v.v_ty;
    ctx_check_e_uid ctx e;
    if not (is_closed v.v_ty) then (
      Error.failf
        (fun k->k"cannot abstract on variable with non closed type %a" pp v.v_ty)
    );
    let db0 = bvar ctx 0 v.v_ty in
    let body = db_shift ctx e 1 in
    subst ~recursive:false ctx body {m=Var.Map.singleton v db0; ty=Var.Map.empty}

  (* replace DB0 in [e] with [u] *)
  let subst_db_0 ctx e ~by:u : t =
    ctx_check_e_uid ctx e;
    ctx_check_e_uid ctx u;

    let cache_ = E_int_tbl.create 8 in

    let rec aux e k : t =
      if is_a_type e then e
      else if db_depth e < k then e
      else (
        match view e with
        | E_const _ -> e
        | E_bound_var bv when bv.bv_idx = k ->
          (* replace here *)
          db_shift ctx u k
        | _ ->
          (* use the cache *)
          try E_int_tbl.find cache_ (e,k)
          with Not_found ->
            let r =
              map ctx e ~f:(fun inb u -> aux u (if inb then k+1 else k))
            in
            E_int_tbl.add cache_ (e,k) r;
            r
      )
    in
    if is_closed e then e else aux e 0

  (* find a name that doesn't capture a variable of [e] *)
  let pick_name_ (name0:string) (e:t) : string =
    let rec loop i =
      let name = if i= 0 then name0 else Printf.sprintf "%s%d" name0 i in
      if free_vars_iter e |> Iter.exists (fun v -> v.v_name = name)
      then loop (i+1)
      else name
    in
    loop 0

  let open_lambda ctx e : _ option =
    match view e with
    | E_lam (name, ty, bod) ->
      let name = pick_name_ name bod in
      let v = Var.make name ty in
      let bod' = subst_db_0 ctx bod ~by:(var ctx v) in
      Some (v, bod')
    | _ -> None

  let open_lambda_exn ctx e = match open_lambda ctx e with
    | Some tup -> tup
    | None ->
      Error.failf (fun k->k"open-lambda: term is not a lambda:@ %a" pp e)

  let arrow ctx a b : t =
    if not (is_a_type a) || not (is_a_type b) then (
      Error.failf (fun k->k"arrow: both arguments must be types");
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_arrow (a,b)) ty

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;

    let ty_f = ty_exn f in
    let ty_a = ty_exn a in

    let[@inline never] fail () =
      Error.failf
        (fun k->
          k"@[<2>kernel: cannot apply function@ `@[%a@]`@ \
           to argument `@[%a@]`@]@];@ \
           @[function has type@ `@[%a@]`,@ \
           but arg has type `@[%a@]`@]"
           pp f pp a pp ty_f pp ty_a)
    in

    let ty =
      match view ty_f with
      | E_arrow (ty_arg, ty_ret) when equal ty_arg ty_a ->
        ty_ret (* no instantiation needed *)
      | _ -> fail()
    in
    let ty = Lazy.from_val (Some ty) in
    let e = make_ ctx (E_app (f,a)) ty in
    e

  let rec app_l ctx f l = match l with
    | [] -> f
    | x :: l' ->
      let f = app ctx f x in
      app_l ctx f l'

  let app_eq ctx a b =
    let f = eq ctx (ty_exn a) in
    let f = app ctx f a in
    let f = app ctx f b in
    f

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let box ctx seq : t =
    let ty = Lazy.from_val (Some (bool ctx)) in
    make_ ctx (E_box seq) ty

  let lambda_db ctx ~name ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    if not (is_a_type ty_v) then (
      Error.failf
        (fun k->k"lambda: variable must have a type as type, not %a"
            pp ty_v);
    );
    let ty = lazy (
      (* type of [λx:a. t] is [a -> typeof(t)] if [a] is a type *)
      Some (arrow ctx ty_v (ty_exn bod))
    ) in
    make_ ctx (E_lam (name, ty_v, bod)) ty

  let lambda ctx v bod =
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~name:v.v_name ~ty_v:v.v_ty bod

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let unfold_app = unfold_app

  let[@inline] unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const ({c_name;_}, [_]), [a;b] when Cname.equal c_name Const.cname_eq ->
      Some(a,b)
    | _ -> None

  let[@unroll 1] rec unfold_arrow e =
    match view e with
    | E_arrow (a,b) ->
      let args, ret = unfold_arrow b in
      a::args, ret
    | _ -> [], e

  let[@unroll 1] rec return_ty e =
    match view e with
    | E_arrow (_,b) -> return_ty b
    | _ -> e

  let[@inline] as_const e = match e.e_view with
    | E_const (c,args) -> Some (c,args)
    | _ -> None

  let[@inline] as_const_exn e = match e.e_view with
    | E_const (c,args) -> c, args
    | _ -> Error.failf (fun k->k"%a is not a constant" pp e)
end

module Subst = struct
  type t = subst = {
    ty: expr Var.Map.t; (* ty subst *)
    m: expr Var.Map.t; (* term subst *)
  }

  let equal a b =
    Var.Map.equal Expr.equal a.ty b.ty &&
    Var.Map.equal Expr.equal a.m b.m

  let hash self : int =
    let hm m =
      CCHash.iter (CCHash.pair Var.hash Expr.hash) (Var.Map.to_iter m)
    in
    CCHash.combine2 (hm self.ty) (hm self.m)

  let[@inline] is_empty self =
    Var.Map.is_empty self.ty &&
    Var.Map.is_empty self.m
  let[@inline] find_exn x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.find x s.ty
    else Var.Map.find x s.m

  let[@inline] mem x s =
    if Expr.is_eq_to_type x.v_ty then Var.Map.mem x s.ty
    else Var.Map.mem x s.m
  let empty = Expr.subst_empty_
  let bind = Expr.subst_bind_
  let pp = Expr.subst_pp_
  let to_list s = List.rev_append (Var.Map.to_list s.ty) (Var.Map.to_list s.m)
  let[@inline] bind' x t s : t = bind s x t
  let[@inline] size self = Var.Map.cardinal self.m + Var.Map.cardinal self.ty
  let[@inline] to_iter self =
    Iter.append (Var.Map.to_iter self.m) (Var.Map.to_iter self.ty)
  let to_string = Fmt.to_string pp

  let is_renaming (self:t) : bool =
    let is_renaming_ m =
      try
        let codom =
          Var.Map.fold
            (fun _v e acc -> match Expr.view e with
               | E_var u -> Var.Set.add u acc
               | _ -> raise_notrace Exit) m Var.Set.empty
        in
        Var.Set.cardinal codom = Var.Map.cardinal m
      with Exit -> false
    in
    is_renaming_ self.ty && is_renaming_ self.m

  let[@inline] bind_uncurry_ s (x,t) = bind s x t
  let of_list = List.fold_left bind_uncurry_ empty
  let of_iter = Iter.fold bind_uncurry_ empty
end

(*$inject
  let ctx = Ctx.create ()
  let bool = Expr.bool ctx
  let type_ = Expr.type_ ctx
  let tau = Expr.const ctx (Ctx.new_skolem_ty_const ctx "tau" ~arity:0) []
  let lambda v t = Expr.lambda ctx v t
  let v' s ty = Var.make s ty
  let v x = Expr.var ctx x
  let (@->) a b = Expr.arrow ctx a b
  let (@@) a b = Expr.app ctx a b
  let a = Expr.const ctx (Ctx.new_skolem_const ctx "a0" [] tau) []
  let b = Expr.const ctx (Ctx.new_skolem_const ctx "b0" [] tau) []
  let c = Expr.const ctx (Ctx.new_skolem_const ctx "c0" [] tau) []
  let f1: const = Ctx.new_skolem_const ctx "f1" [] (tau @-> tau)
  let eq = Expr.app_eq ctx

  let must_fail f = try ignore (f()); false with _ -> true
*)

(*$T
  must_fail (fun() -> a @-> b)
  Expr.equal (tau @-> bool) (tau @-> bool)
*)


(** {2 Toplevel goals} *)
module Sequent = struct
  type t = sequent = {
    concl: Expr.t;
    hyps: expr_set;
  }

  let equal = sequent_eq
  let hash = sequent_hash
  let make hyps concl : t = {hyps; concl}
  let make_l h c = make (Expr_set.of_list h) c
  let make_nohyps c : t = make Expr_set.empty c

  let[@inline] chash self : Chash.t =
    Chash.run Util_chash_.hasher_seq_ self

  let[@inline] concl g = g.concl
  let[@inline] n_hyps self = Int_map.cardinal self.hyps
  let[@inline] hyps g = g.hyps
  let[@inline] hyps_iter g = Expr_set.to_iter g.hyps
  let[@inline] hyps_l g = Expr_set.to_list g.hyps

  let iter_exprs self =
    Iter.cons (concl self) (hyps_iter self)

  let pp out (self:t) : unit =
    if Expr_set.is_empty self.hyps then (
      Fmt.fprintf out "@[?-@ %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<hv>%a@ ?-@ %a@]"
        (pp_iter ~sep:", " Expr.pp) (hyps_iter self)
        Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
end

(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx = struct
  type t = ctx

  let uid_ = ref 0

  let create
      ?(storage=Storage.in_memory ())
      ?(store_proofs=false)
      ?(store_concrete_definitions=false)
      () : t =
    let ctx_uid = !uid_ land ctx_id_mask in
    incr uid_;
    let rec ctx = {
      ctx_uid;
      ctx_store_concrete_definitions=store_concrete_definitions;
      ctx_store_proofs=store_proofs;
      ctx_storage=storage;
      ctx_exprs=Expr_hashcons.create ~size:2_048 ();
      ctx_axioms=[];
      ctx_axioms_allowed=true;
      ctx_kind=lazy (Expr.make_ ctx E_kind (Lazy.from_val None));
      ctx_type=lazy (
        let kind = Expr.kind ctx in
        Expr.make_ ctx E_type (Lazy.from_val (Some kind))
      );
      ctx_bool_c=lazy (
        let typ = Expr.type_ ctx in
        let c = Const.make ctx id_bool ~def:(C_def_magic id_bool) (C_arity 0) typ in
        assert (Cname.equal c.c_name Const.cname_bool);
        c
      );
      ctx_bool=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_bool_c) []
      );
      ctx_eq_c=lazy (
        let type_ = Expr.type_ ctx in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx ea @@ arrow ctx ea @@ bool ctx) in
        let c = Const.make ctx id_eq ~def:(C_def_magic id_eq) (C_ty_vars [a_]) typ in
        assert (Cname.equal c.c_name Const.cname_eq);
        c
      );
      ctx_select_c=lazy (
        let type_ = Expr.type_ ctx in
        let lazy bool_ = ctx.ctx_bool in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx (arrow ctx ea bool_) ea) in
        let c =
          Const.make ctx id_select ~def:(C_def_magic id_select) (C_ty_vars [a_]) typ in
        assert (Cname.equal c.c_name Const.cname_select);
        c
      );
    } in
    ctx

  let n_exprs self = Expr_hashcons.size self.ctx_exprs

  let pledge_no_more_axioms self =
    if self.ctx_axioms_allowed then (
      Log.debugf 5 (fun k->k "pledge no more axioms");
      self.ctx_axioms_allowed <- false;
    )

  let axioms self k = List.iter k self.ctx_axioms

  let new_skolem_const self name tyvars ty : const =
    Const.make self ~def:(C_def_skolem {name}) name (C_ty_vars tyvars) ty

  let new_skolem_ty_const self name ~arity : const =
    let ty = Expr.type_ self in
    Const.make self ~def:(C_def_skolem_ty {name; arity}) name (C_arity arity) ty
end

module New_ty_def = struct
  type t = {
    tau: ty_const;
    (** the new type constructor *)
    fvars: var list;
    c_abs: const;
    (** Function from the general type to `tau` *)
    c_repr: const;
    (** Function from `tau` back to the general type *)
    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)
    abs_x: var;
    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)
    repr_x: var;
  }
end

(** {2 Theorems and Deduction Rules} *)

module Proof = struct
  type t = proof =
    | Pr_dummy
    | Pr_main of proof
    | Pr_step of {
        rule: string;
        args: proof_arg list;
        parents: thm list;
      }

  type arg = proof_arg =
    | Pr_expr of expr
    | Pr_subst of (var * expr) list

  let a_expr e : arg = Pr_expr e
  let a_subst (s:subst) : arg = Pr_subst (Subst.to_list s)

  let dummy : t = Pr_dummy
  let main self : t = Pr_main self
  let step ?(args=[]) ?(parents=[]) (rule:string) : t =
    Pr_step {rule; args; parents}

  let is_main = function Pr_main _ -> true | _ -> false
  let is_main_or_dummy = function
    | Pr_dummy | Pr_main _ -> true
    | Pr_step _ -> false
end

module Thm = struct
  type t = thm

  let[@inline] concl self = self.th_seq.concl
  let[@inline] sequent self = self.th_seq
  let[@inline] hyps_ self = self.th_seq.hyps
  let[@inline] hyps_iter self k = Expr_set.iter k self.th_seq.hyps
  let[@inline] hyps_l self = Expr_set.to_list self.th_seq.hyps
  let hyps_sorted_l = hyps_l
  let iter_exprs self = Sequent.iter_exprs self.th_seq
  let[@inline] has_hyps self = not (Expr_set.is_empty self.th_seq.hyps)
  let n_hyps self = Expr_set.size self.th_seq.hyps

  let is_fully_concrete self =
    Const.expr_is_concrete_ (concl self) &&
    Iter.for_all Const.expr_is_concrete_ (hyps_iter self)

  let rec chash_proof_ ctx =
    let open Chash in
    function
    | Pr_main p -> string ctx "m"; chash_proof_ ctx p
    | Pr_dummy -> string ctx "d";
    | Pr_step {rule; args=_; parents} ->
      (* TODO: hash args, too, although hashing the conclusion might be enough *)
      string ctx "s";
      string ctx rule;
      List.iter (fun th -> Util_chash_.hasher_seq_ ctx th.th_seq) parents

  let chash self =
    let open Chash in
    let ctx = create() in
    Util_chash_.hasher_seq_ ctx self.th_seq;
    chash_proof_ ctx self.th_proof;
    finalize ctx

  let proof self = self.th_proof

  let make_main_proof self =
    if not (Proof.is_main_or_dummy self.th_proof) then (
      self.th_proof <- Pr_main self.th_proof;
    )

  let[@inline] equal a b = Sequent.equal a.th_seq b.th_seq

  let hash (self:t) = Sequent.hash self.th_seq

  module Tbl = CCHashtbl.Make(struct
      type t = thm
      let equal = equal
      let hash = hash
    end)

  type 'a with_ctx = ctx -> 'a

  let pp_depth ~max_depth out (th:t) =
    let pp_t = Expr.pp_depth ~max_depth in
    if has_hyps th then (
      Fmt.fprintf out "@[<hv1>%a@;<1 -1>|-@ %a@]" (pp_list ~sep:", " pp_t)  (hyps_l th)
        pp_t (concl th)
    ) else (
      Fmt.fprintf out "@[<1>|-@ %a@]" pp_t (concl th)
    )

  let pp = pp_depth ~max_depth:max_int

  let to_string = Fmt.to_string pp
  let pp_quoted = Fmt.within "`" "`" pp

  let is_proof_of self (g:Sequent.t) : bool =
    Expr.equal self.th_seq.concl (Sequent.concl g) &&
    Expr_set.subset self.th_seq.hyps (Sequent.hyps g)

  (** {3 Deduction rules} *)

  let make_seq_ ctx seq proof th_theory : t =
    let th_flags = ctx.ctx_uid in
    let proof = if ctx.ctx_store_proofs then proof () else Proof.dummy in
    { th_flags; th_seq=seq; th_proof=proof; th_theory }

  let make_ ctx hyps concl proof th : t =
    let th_seq = Sequent.make hyps concl in
    make_seq_ ctx th_seq proof th

  let is_bool_ ctx e : bool =
    let ty = Expr.ty_exn e in
    Expr.equal (Expr.bool ctx) ty

  let assume ctx (e:Expr.t) : t =
    Error.guard (fun err -> Error.wrapf "in assume `@[%a@]`:" Expr.pp e err) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not (is_bool_ ctx e) then (
      Error.fail "assume takes a boolean"
    );
    let proof () =
      Proof.(step "assume" ~args:[a_expr e])
    in
    make_ ctx (Expr_set.singleton e) e proof None

  let axiom ctx hyps e : t =
    Error.guard (fun err ->
        let g = Sequent.make_l hyps e in
        Error.wrapf "in axiom `@[%a@]`:" Sequent.pp g err) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not ctx.ctx_axioms_allowed then (
      Error.fail "the context does not accept new axioms, see `pledge_no_more_axioms`"
    );
    if not (is_bool_ ctx e && List.for_all (is_bool_ ctx) hyps) then (
      Error.fail "axiom takes a boolean"
    );
    let proof () =
      Proof.(step "axiom" ~args:[a_expr e]) in
    make_ ctx (Expr_set.of_list hyps) e proof None

  let merge_hyps_ = Expr_set.union

  let merge_theory_ a b = match a, b with
    | None, a -> a
    | a, None -> a
    | Some a as res, Some b ->
      if a != b then Error.fail "cannot use theorems from distinct theories";
      res

  let cut ctx th1 th2 : t =
    Error.guard
      (fun e -> Error.wrapf "@[<2>in cut@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2 e)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let b = concl th1 in
    let hyps = merge_hyps_ (hyps_ th1) (Expr_set.remove b (hyps_ th2)) in
    let proof () = Proof.(step "cut" ~parents:[th1; th2]) in
    let th = merge_theory_ th1.th_theory th2.th_theory in
    make_ ctx hyps (concl th2) proof th

  let refl ctx e : t =
    ctx_check_e_uid ctx e;
    let proof () = Proof.(step "refl" ~args:[a_expr e]) in
    make_ ctx Expr_set.empty (Expr.app_eq ctx e e) proof None

  let congr ctx th1 th2 : t =
    Error.guard
      (fun err -> Error.wrapf "@[<2>in congr@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2 err)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> Error.fail "th1 is non equational"
    | _, None -> Error.fail "th2 is non equational"
    | Some (f,g), Some (t,u) ->
      let t1 = Expr.app ctx f t in
      let t2 = Expr.app ctx g u in
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      let proof () = Proof.(step "congr" ~parents:[th1;th2]) in
      let th = merge_theory_ th1.th_theory th2.th_theory in
      make_ ctx hyps (Expr.app_eq ctx t1 t2) proof th

  exception E_subst_non_closed of var * expr

  let subst ~recursive ctx th s : t =
    begin try
        Var.Map.iter (fun v t ->
            if not (Expr.is_closed t) then raise_notrace (E_subst_non_closed (v,t)))
          s.m
      with
      | E_subst_non_closed (v,t) ->
        Error.failf(fun k->k"subst: variable %a@ is bound to non-closed term %a"
                  Var.pp v Expr.pp t)
    end;
    let hyps = hyps_ th |> Expr_set.map (fun e -> Expr.subst ~recursive ctx e s) in
    let concl = Expr.subst ~recursive ctx (concl th) s in
    let proof() = Proof.(step "subst" ~args:[a_subst s] ~parents:[th]) in
    make_ ctx hyps concl proof th.th_theory

  let sym ctx th : t =
    Error.guard (fun err -> Error.wrapf "@[<2>in sym@ `@[%a@]`@]:" pp th err) @@ fun () ->
    ctx_check_th_uid ctx th;
    match Expr.unfold_eq (concl th) with
    | None -> Error.failf (fun k->k"sym: concl of %a@ should be an equation" pp th)
    | Some (t,u) ->
      let proof () = Proof.(step "sym" ~parents:[th]) in
      make_ ctx (hyps_ th) (Expr.app_eq ctx u t) proof th.th_theory

  let trans ctx th1 th2 : t =
    Error.guard
      (fun err -> Error.wrapf "@[<2>in trans@ %a@ %a@]:" pp_quoted th1 pp_quoted th2 err)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> Error.failf (fun k->k"trans: concl of %a@ should be an equation" pp th1)
    | _, None -> Error.failf (fun k->k"trans: concl of %a@ should be an equation" pp th2)
    | Some (t,u), Some (u',v) ->
      if not (Expr.equal u u') then (
        Error.failf (fun k->k"@[<2>kernel: trans: conclusions@ \
                         of %a@ and %a@ do not match@]" pp th1 pp th2)
      );
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      let proof() = Proof.(step "trans" ~parents:[th1;th2]) in
      let th = merge_theory_ th1.th_theory th2.th_theory in
      make_ ctx hyps (Expr.app_eq ctx t v) proof th

  let bool_eq ctx th1 th2 : t =
    Error.guard
      (fun err -> Error.wrapf "@[<hv2>in bool_eq@ th1=%a@ th2=%a@]:"
         pp_quoted th1 pp_quoted th2 err)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th2) with
    | None ->
      Error.failf (fun k->k"bool-eq should have a boolean equality as conclusion in %a"
                 pp th2)
    | Some (t, u) ->
      if Expr.equal t (concl th1) then (
        let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
        let proof() = Proof.(step "bool_eq" ~parents:[th1;th2]) in
        let th = merge_theory_ th1.th_theory th2.th_theory in
        make_ ctx hyps u proof th
      ) else (
        Error.failf
          (fun k->k
              "bool-eq: mismatch,@ conclusion of %a@ does not match LHS of %a@ \
               (lhs is: `@[%a@]`)"
              pp_quoted th1 pp_quoted th2 Expr.pp t)
      )

  let bool_eq_intro ctx th1 th2 : t =
    Error.guard
      (fun err -> Error.wrapf "@[<2>in bool_eq_intro@ th1=`@[%a@]`@ th2=`@[%a@]`@]:"
         pp th1 pp th2 err)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let e1 = concl th1 in
    let e2 = concl th2 in
    let hyps =
      merge_hyps_
        (Expr_set.remove e1 (hyps_ th2))
        (Expr_set.remove e2 (hyps_ th1))
    in
    let proof() = Proof.(step "bool_eq_intro" ~parents:[th1;th2]) in
    let th = merge_theory_ th1.th_theory th2.th_theory in
    make_ ctx hyps (Expr.app_eq ctx e1 e2) proof th

  let beta_conv ctx e : t =
    Error.guard (fun err -> Error.wrapf "@[<2>in beta-conv `@[%a@]`:" Expr.pp e err) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.view e with
    | E_app (f, a) ->
      (match Expr.view f with
       | E_lam (_, ty_v, body) ->
         assert (Expr.equal ty_v (Expr.ty_exn a)); (* else `app` would have failed *)
         let rhs = Expr.subst_db_0 ctx body ~by:a in
         let proof() = Proof.(step "beta_conv" ~args:[a_expr e]) in
         make_ ctx Expr_set.empty (Expr.app_eq ctx e rhs) proof None
       | _ ->
         Error.failf (fun k->k"not a redex: function %a is not a lambda" Expr.pp f)
      )
    | _ ->
      Error.failf (fun k->k"not a redex: %a not an application" Expr.pp e)

  let abs ctx v th : t =
    Error.guard (fun err -> Error.wrapf "@[<2>in abs :var %a `@[%a@]`:" Var.pp v pp th err) @@ fun () ->
    ctx_check_th_uid ctx th;
    ctx_check_e_uid ctx v.v_ty;
    match Expr.unfold_eq th.th_seq.concl with
    | Some (a,b) ->
      let is_in_hyp hyp = Iter.mem ~eq:Var.equal v (Expr.free_vars_iter hyp) in
      if Expr_set.exists is_in_hyp th.th_seq.hyps then (
        Error.failf (fun k->k"variable `%a` occurs in an hypothesis@ of %a" Var.pp v pp th);
      );
      let proof() = Proof.(step "abs" ~parents:[th]) in
      make_ ctx th.th_seq.hyps
        (Expr.app_eq ctx (Expr.lambda ctx v a) (Expr.lambda ctx v b)) proof th.th_theory
    | None -> Error.failf (fun k->k"conclusion of `%a`@ is not an equation" pp th)

  let new_basic_definition ctx (e:expr) : t * const =
    Error.guard (fun err -> Error.wrapf "@[<2>in new-basic-def@ `@[%a@]`@]:" Expr.pp e err) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.unfold_eq e with
    | None ->
      Error.failf (fun k->k"new-basic-def: expect an equation `x=rhs`,@ got %a" Expr.pp e)
    | Some (x, rhs) ->
      if Expr.contains rhs ~sub:x then (
        Error.failf (fun k->k"RHS %a@ contains variable %a" Expr.pp rhs Expr.pp x)
      );
      if not (Expr.is_closed rhs) then (
        Error.failf (fun k->k"RHS %a@ is not closed" Expr.pp rhs);
      );
      let x_var = match Expr.view x with
        | E_var v -> v
        | _ ->
          Error.failf (fun k-> k "LHS must be a variable,@ but got %a" Expr.pp x)
      in

      let fvars = Expr.free_vars rhs in
      let ty_vars_l = Var.Set.to_list fvars in
      begin match List.find (fun v -> not (Expr.is_eq_to_type v.v_ty)) ty_vars_l with
        | v ->
          Error.failf
            (fun k->k"RHS contains free variable `@[%a : %a@]`@ which is not a type variable"
                Var.pp v Expr.pp v.v_ty)
        | exception Not_found -> ()
      end;

      let c = Expr.new_const ctx
          ~def:(C_def_expr {vars=ty_vars_l; rhs})
          (Var.name x_var) ty_vars_l (Var.ty x_var) in
      let c_e = Expr.const ctx c (List.map (Expr.var ctx) ty_vars_l) in
      let proof() = Proof.(step "new_def" ~args:[a_expr e]) in
      let th = make_ ctx Expr_set.empty (Expr.app_eq ctx c_e rhs) proof None in
      th, c

  let new_basic_type_definition ctx
      ?ty_vars:provided_ty_vars
      ~name ~abs ~repr ~thm_inhabited () : New_ty_def.t =
    Error.guard
      (fun err -> Error.wrapf "@[<2>in new-basic-ty-def :name %s@ :thm `@[%a@]`@]:"
         name pp thm_inhabited err)
    @@ fun () ->
    ctx_check_th_uid ctx thm_inhabited;
    if has_hyps thm_inhabited then (
      Error.failf (fun k->k"theorem %a must not have any hypothesis" pp thm_inhabited);
    );
    let phi, witness = match Expr.view (concl thm_inhabited) with
      | E_app (phi,w) -> phi, w
      | _ ->
        Error.failf (fun k->k"expected conclusion of theorem %a@ to be an application"
                   pp thm_inhabited);
    in
    (* the concrete type *)
    let ty = Expr.ty_exn witness in
    (* check that all free variables in [phi] are type variables *)
    let fvars_phi = Expr.free_vars phi in
    let all_ty_fvars =
      Expr.free_vars_iter witness
      |> Iter.filter (fun v -> Expr.is_eq_to_type v.v_ty)
      |> Var.Set.add_iter fvars_phi
    in
    begin match
        Var.Set.find_first (fun v -> not (Expr.is_eq_to_type (Var.ty v))) fvars_phi
      with
      | v ->
        Error.failf (fun k->k"free variable %a@ occurs in Phi (in `|- Phi t`)@ \
                         and it is not a type variable" Var.pp_with_ty v)
      | exception Not_found -> ()
    end;

    let ty_vars_l = match provided_ty_vars with
      | None -> Var.Set.to_list all_ty_fvars (* pick any order *)
      | Some l ->
        if not (Var.Set.equal all_ty_fvars (Var.Set.of_list l)) then (
          Error.failf
            (fun k->k
                "list of type variables (%a) in new-basic-ty-def@ does not match %a"
                (Fmt.Dump.list Var.pp) (Var.Set.to_list all_ty_fvars)
                (Fmt.Dump.list Var.pp) l);
        );
        l
    in
    let ty_vars_expr_l = ty_vars_l |> CCList.map (Expr.var ctx) in

    Log.debugf 5
      (fun k->k"(@[new-basic-ty-def@ :name `%s`@ :phi %a@ \
                :ty-vars %a@ :repr `%s`@ :abs `%s`@])"
           name pp_quoted thm_inhabited (Fmt.Dump.list Var.pp) ty_vars_l repr abs);

    let arity = List.length ty_vars_l in

    (* construct new type and mapping functions *)
    let tau = Expr.new_ty_const ~def:(C_def_ty {arity; phi}) ctx name arity in
    let tau_vars = Expr.const ctx tau ty_vars_expr_l in

    let c_abs =
      let ty = Expr.arrow ctx ty tau_vars in
      Expr.new_const ~def:(C_def_ty_abs {arity; phi}) ctx abs ty_vars_l ty
    in
    let c_repr =
      let ty = Expr.arrow ctx tau_vars ty in
      Expr.new_const ~def:(C_def_ty_repr {arity; phi}) ctx repr ty_vars_l ty
    in

    let proof() = Proof.(step "new_ty" ~args:[a_expr phi]) in

    let abs_x = Var.make "x" tau_vars in
    (* `|- abs (repr x) = x` *)
    let abs_thm =
      let abs_x = Expr.var ctx abs_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t = Expr.app ctx repr abs_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let abs_t = Expr.app ctx abs t in
      let eqn = Expr.app_eq ctx abs_t abs_x in
      make_ ctx Expr_set.empty eqn proof None
    in

    let repr_x = Var.make "x" ty in
    (* `|- Phi x <=> repr (abs x) = x` *)
    let repr_thm =
      let repr_x = Expr.var ctx repr_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let t1 = Expr.app ctx abs repr_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t2 = Expr.app ctx repr t1 in
      let eq_t2_x = Expr.app_eq ctx t2 repr_x in
      let phi_x = Expr.app ctx phi repr_x in
      make_ ctx Expr_set.empty (Expr.app_eq ctx phi_x eq_t2_x) proof None
    in

    {New_ty_def.
      tau; c_repr; c_abs; fvars=ty_vars_l; repr_x;
      repr_thm; abs_x; abs_thm}

  let box ctx (th: t) : t =
    let box = Expr.box ctx th.th_seq in
    let proof() = Proof.(step "box" ~parents:[th]) in
    make_ ctx Expr_set.empty box proof th.th_theory

  let assume_box ctx (seq:sequent) : t =
    let box = Expr.box ctx seq in
    let seq' = {seq with hyps=Expr_set.add box seq.hyps} in
    let proof() = Proof.(step "assume-box") in
    make_seq_ ctx seq' proof None
end

module Theory = struct
  type t = theory

  let name self = self.theory_name
  let param_consts self = Name_k_map.values self.theory_in_constants |> Iter.to_list
  let param_theorems self = self.theory_in_theorems
  let consts self = Name_k_map.values self.theory_defined_constants |> Iter.to_list
  let theorems self = self.theory_defined_theorems

  let pp_name out self = Fmt.string out self.theory_name
  let pp out (self:t) : unit =
    let {theory_name=name; theory_ctx=_; theory_in_constants=inc;
         theory_in_theorems=inth; theory_defined_theorems=dth;
         theory_defined_constants=dc; } = self in
    Fmt.fprintf out "(@[<v1>theory %a" Fmt.string name;
    Name_k_map.iter (fun _ c ->
        Fmt.fprintf out "@,(@[in-const@ %a@])" Const.pp_with_ty c)
      inc;
    List.iter (fun th -> Fmt.fprintf out "@,(@[in-thm@ %a@])" Thm.pp_quoted th) inth;
    Name_k_map.iter
      (fun _ c ->
         Fmt.fprintf out "@,(@[defined-const@ %a@])" Const.pp_with_ty c)
      dc;
    List.iter (fun th -> Fmt.fprintf out "@,(@[defined-thm@ %a@])" Thm.pp_quoted th) dth;
    Fmt.fprintf out "@])";
    ()

  let to_string = Fmt.to_string pp

  let assume self hyps concl : thm =
    let ctx = self.theory_ctx in
    Error.guard
      (fun err -> Error.wrapf "in theory_assume@ `@[%a@ |- %a@]`:" (pp_list Expr.pp) hyps Expr.pp concl err)
    @@ fun () ->
    if not (Thm.is_bool_ ctx concl && List.for_all (Thm.is_bool_ ctx) hyps) then (
      Error.fail "Theory.assume: all terms must be booleans"
    );
    let hyps = Expr_set.of_list hyps in
    let proof() = Proof.(step "th.assume") in
    let th = Thm.make_ ctx hyps concl proof (Some self) in
    self.theory_in_theorems <- th :: self.theory_in_theorems;
    th

  let add_assumption_const self (c:const) : unit =
    let kind = if Expr.is_eq_to_type c.c_ty then C_ty else C_term in
    if Name_k_map.mem (kind,Cname.name c.c_name) self.theory_in_constants then (
      Error.failf (fun k->k"Theory.assume_const: constant `%a` already exists"
      Cname.pp_name c.c_name);
    );
    self.theory_in_constants <-
      Name_k_map.add (kind,Cname.name c.c_name) c self.theory_in_constants;
    ()

  let assume_const self name ty_vars ty : const =
    let c = Expr.new_const
        ~def:(C_def_theory_param {ty_vars;ty})
        self.theory_ctx name ty_vars ty in
    add_assumption_const self c;
    c

  let assume_ty_const self name ~arity : const =
    let c = Expr.new_ty_const self.theory_ctx name arity
        ~def:(C_def_theory_ty_param {arity}) in
    add_assumption_const self c;
    c

  let add_const_ self c : unit =
    let key = Cname.name c.c_name in
    let kind = if Expr.is_eq_to_type c.c_ty then C_ty else C_term in
    begin match Name_k_map.get (kind,key) self.theory_defined_constants with
      | Some c' when Const.equal c c' ->
        Log.debugf 2 (fun k->k"redef `%a`" Fmt.string key);
      | Some _ ->
        Error.failf (fun k->k"Theory.add_const: constant `%a` already defined" Fmt.string key);
      | None -> ()
    end;
    self.theory_defined_constants <- Name_k_map.add (kind,key) c self.theory_defined_constants

  let add_const = add_const_
  let add_ty_const = add_const_

  let[@inline] find_const self s : _ option =
    try Some (Name_k_map.find (C_term,s) self.theory_defined_constants)
    with Not_found -> Name_k_map.get (C_term,s) self.theory_in_constants

  let[@inline] find_ty_const self s : _ option =
    try Some (Name_k_map.find (C_ty,s) self.theory_defined_constants)
    with Not_found -> Name_k_map.get (C_ty,s) self.theory_in_constants

  let add_theorem self th : unit =
    (match th.th_theory with
    | None -> th.th_theory <- Some self
    | Some th' when self != th' ->
        Error.failf (fun k->k"add theorem %a@ from the wrong theory" Thm.pp th)
    | Some _ -> ());
    self.theory_defined_theorems <- th :: self.theory_defined_theorems

  let mk_ ctx ~name : t =
    { theory_name=name; theory_ctx=ctx;
      theory_in_constants=Name_k_map.empty;
      theory_defined_constants=Name_k_map.empty;
      theory_in_theorems=[]; theory_defined_theorems=[]
    }

  let mk_str_ ctx ~name : t =
    mk_ ctx ~name

  let with_ ctx ~name f : t =
    let self = mk_str_ ctx ~name in
    f self;
    self

  (* check that all theories in [l] come from context [ctx] *)
  let check_same_ctx_ ctx l =
    List.iter
      (fun th -> if th.theory_ctx != ctx
        then Error.failf (fun k->k"theory `%a` comes from a different context" pp_name th))
      l

  let union_const_map_ ~what m1 m2 =
    Name_k_map.union
      (fun (_,n) c1 c2 ->
         if not (Const.equal c1 c2) then (
           Error.failf (fun k->k"incompatible %s constant `%a`: %a vs %a"
                      what Fmt.string n Const.pp c1 Const.pp c2)
         );
         Some c1)
      m1 m2

  (* FIXME: update theorems' theory pointer? *)
  let union ctx ~name l : t =
    check_same_ctx_ ctx l;
    let self = mk_str_ ctx ~name in
    let in_th =
      Iter.of_list self.theory_in_theorems |> Iter.map (fun th -> th,())
      |> Thm.Tbl.of_iter_with ~f:(fun _ () () -> ())
    and out_th =
      Iter.of_list self.theory_defined_theorems |> Iter.map (fun th -> th,())
      |> Thm.Tbl.of_iter_with ~f:(fun _ () () -> ())
    in
    List.iter
      (fun th ->
        self.theory_in_constants <-
          union_const_map_ ~what:"assumed"
            self.theory_in_constants th.theory_in_constants;
        self.theory_defined_constants <-
          union_const_map_ ~what:"defined"
            self.theory_defined_constants th.theory_defined_constants;
        List.iter (fun th -> Thm.Tbl.replace in_th th ()) th.theory_in_theorems;
        List.iter (fun th -> Thm.Tbl.replace out_th th ()) th.theory_defined_theorems;
      )
      l;
    self.theory_in_theorems <-
      in_th |> Thm.Tbl.to_iter |> Iter.map fst |> Iter.to_rev_list;
    self.theory_defined_theorems <-
      out_th |> Thm.Tbl.to_iter |> Iter.map fst |> Iter.to_rev_list;
    self

  (* interpretation: map some constants to other constants *)
  type interpretation = string Str_map.t

  let pp_interp out (i:interpretation) : unit =
    let pp_pair out (n,u) = Fmt.fprintf out "(@[`%s` =>@ `%s`@])" n u in
    Fmt.fprintf out "{@[%a@]}"
      (Fmt.iter ~sep:(Fmt.return "@ ") pp_pair) (Str_map.to_iter i)

  module Instantiate_ = struct
    type state = {
      ctx: Ctx.t;
      cache: expr Expr.Tbl.t;
      interp: interpretation;
      find_const: string -> ty:Expr.t -> const option;
      (* context in which to try to reinterpret constants *)
    }

    let create
        ?(find_const=fun _ ~ty:_ -> None)
        ?(interp=Str_map.empty) ctx : state =
      { ctx; interp; cache=Expr.Tbl.create 32; find_const; }

    (* instantiate one term *)
    let rec inst_t_ (self:state) (e:expr) : expr =
      let rec loop e =
        match Expr.Tbl.find self.cache e with
        | u -> u
        | exception Not_found ->
          let u =
            match Expr.view e with
            | E_var v -> Expr.var self.ctx (Var.map_ty v ~f:loop)
            | E_const (c, args) ->
              let args' = List.map loop args in
              let c' = inst_const_ self c in
              if Const.equal c c' && List.for_all2 Expr.equal args args'
              then e
              else Expr.const self.ctx c' args'
            | _ ->
              Expr.map self.ctx e ~f:(fun _ e' -> loop e')
          in
          Expr.Tbl.add self.cache e u;
          u
      in
      loop e

    and inst_const_ (self:state) (c:const) : const =
      let ty' = inst_t_ self c.c_ty in
      let name' =
        try Str_map.find (Cname.name c.c_name) self.interp
        with Not_found -> Cname.name c.c_name
      in
      (* reinterpret constant? *)
      begin match self.find_const name' ~ty:ty' with
        | Some c' when Expr.is_eq_to_type c'.c_ty -> c'
        | Some c' ->
          let c'_def = Const.get_def_exn self.ctx c' in
          (* reinterpret into [c']… whose type might also change *)
          let ty'' = inst_t_ self c'.c_ty in
          let def = Const_def.map c'_def ~f:(inst_t_ self) in
          let chash =
            if Const.is_concrete_def def then Some c'.c_name.chash else None in
          Const.make self.ctx ~def ?chash (Cname.name c'.c_name) c'.c_args ty''
        | None ->
          let c_def = Const.get_def_exn self.ctx c in
          let def = Const_def.map c_def ~f:(inst_t_ self) in
          let chash =
            if Const.is_concrete_def def then Some c.c_name.chash else None in
          Const.make self.ctx ~def ?chash name' c.c_args ty'
      end

    let inst_constants_ (self:state) (m:const Name_k_map.t) : _ Name_k_map.t =
      Name_k_map.to_iter m
      |> Iter.map
        (fun ((k,_),c) ->
           let c' = inst_const_ self c in
           (k,c'.c_name.name), c')
      |> Name_k_map.of_iter

    (* instantiate a whole theorem *)
    let inst_thm_ (self:state) theory (th:thm) : thm =
      let hyps =
        Expr_set.to_iter th.th_seq.hyps
        |> Iter.map (inst_t_ self)
        |> Expr_set.of_iter
      in
      let concl = inst_t_ self th.th_seq.concl in
      let proof() = th.th_proof in
      Thm.make_ self.ctx hyps concl proof (Some theory)

    let inst_theory_ (self:state) (th:theory) : theory =
      assert (self.ctx == th.theory_ctx);
      let {
        theory_ctx=_; theory_name; theory_in_constants;
        theory_in_theorems; theory_defined_constants;
        theory_defined_theorems} = th in
      let th' = mk_ self.ctx ~name:theory_name in
      th'.theory_in_constants <-
        inst_constants_ self theory_in_constants;
      th'.theory_defined_constants <-
        inst_constants_ self theory_defined_constants;
      th'.theory_in_theorems <-
        List.map (inst_thm_ self th') theory_in_theorems;
      th'.theory_defined_theorems <-
        List.map (inst_thm_ self th') theory_defined_theorems;
      th'
  end

  let instantiate ~(interp:interpretation) th : t =
    if Str_map.is_empty interp then th
    else (
      let st = Instantiate_.create ~interp th.theory_ctx in
      Instantiate_.inst_theory_ st th
    )

  (* index by name+ty, for constants *)
  module Str_ty_tbl = CCHashtbl.Make(struct
      type t = string * Expr.t
      let equal (n1,ty1) (n2,ty2) = String.equal n1 n2 && Expr.equal ty1 ty2
      let hash (n,ty) = H.(combine3 25 (H.string n) (Expr.hash ty))
    end)

  let compose ?(interp=Str_map.empty) l th : t =
    Log.debugf 2
      (fun k->k"(@[theory.compose@ %a@ %a@ @[:interp %a@]@])"
          Fmt.(Dump.list pp_name) l pp_name th pp_interp interp);

    if CCList.is_empty l then (
      instantiate ~interp th
    ) else (
      let ctx = th.theory_ctx in

      (* reinterpret constants that are provided by [l]. For that we need
         to index them by [name,ty].
         Also gather the set of proved theorems from *)
      let const_tbl_ = Str_ty_tbl.create 32 in
      let provided_thms = Thm.Tbl.create 32 in

      List.iter
        (fun th0 ->
           Name_k_map.iter (fun _ c -> Str_ty_tbl.replace const_tbl_ (c.c_name.name,c.c_ty) c)
             th0.theory_in_constants;
           Name_k_map.iter (fun _ c -> Str_ty_tbl.replace const_tbl_ (c.c_name.name,c.c_ty) c)
             th0.theory_defined_constants;
           List.iter (fun th -> Thm.Tbl.replace provided_thms th ())
             th0.theory_defined_theorems;
        )
        l;

      let find_const name ~ty = Str_ty_tbl.get const_tbl_ (name,ty) in

      let st = Instantiate_.create ~find_const ~interp ctx in
      let th = Instantiate_.inst_theory_ st th in

      (* remove provided constants *)
      th.theory_in_constants <-
        Name_k_map.filter
          (fun _ c ->
            not (Str_ty_tbl.mem const_tbl_ (c.c_name.name,c.c_ty)))
          th.theory_in_constants;
      (* remove satisfied assumptions *)
      let in_thm =
        th.theory_in_theorems
        |> Iter.of_list
        |> Iter.filter (fun thm -> not (Thm.Tbl.mem provided_thms thm))
        |> Iter.map (fun thm -> thm, ())
        |> Thm.Tbl.of_iter
      in
      (* add assumptions from [l] *)
      List.iter (fun th' ->
          List.iter
            (fun thm -> Thm.Tbl.replace in_thm thm ())
            th'.theory_in_theorems)
        l;
      th.theory_in_theorems <-
        Thm.Tbl.to_iter in_thm |> Iter.map fst
        |> Iter.to_rev_list;

      th
    )
end

(* ok def *)
(*$R
  let a_ = v' "a" type_ in
  let ok_def, _thm =
    Thm.new_basic_definition ctx
      (let thevar = v (v' "body" (v a_ @-> v a_)) in
       let x = v' "x" (v a_) in
       eq thevar (lambda x (v x)))
  in
  ()
*)

