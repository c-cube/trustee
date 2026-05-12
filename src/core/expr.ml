open Types
open Sigs
module H = CCHash
module CB = Cbor_pack

(* ── Expr0: basic expr interface ── *)

module Expr0 = struct
  type t = expr

  let[@inline] ty e =
    match e.e_ty with Ty t -> Some t | _ -> None
  let[@inline] view e = e.e_view

  let[@inline] ty_exn e =
    match e.e_ty with
    | Ty t -> t
    | _ -> assert false

  let equal = expr_eq
  let hash = expr_hash

  module AsKey = struct
    type nonrec t = t

    let equal = equal
    let compare = expr_compare
    let hash = hash
  end

  module Map = CCMap.Make (AsKey)
  module Set = CCSet.Make (AsKey)
  module Tbl = CCHashtbl.Make (AsKey)

  let iter ~f (e : expr) : unit =
    match e.e_view with
    | E_kind | E_type -> ()
    | _ ->
      (match e.e_ty with
      | Ty ty -> f false ty
      | _ -> ());
      (match e.e_view with
      | E_box _ | E_const _ -> ()
      | E_kind | E_type -> assert false
      | E_var v -> f false v.v_ty
      | E_bound_var v -> f false v.bv_ty
      | E_app (hd, a) ->
        f false hd;
        f false a
      | E_lam (_, tyv, bod) ->
        f false tyv;
        f true bod
      | E_arrow (a, b) ->
        f false a;
        f false b)

  let iter_dag ~iter_ty ~f e : unit =
    let tbl = Tbl.create 8 in
    let rec loop e =
      if not (Tbl.mem tbl e) then (
        Tbl.add tbl e ();
        if iter_ty then (match e.e_ty with Ty t -> loop t | _ -> ());
        f e;
        iter e ~f:(fun _ u -> loop u)
      )
    in
    loop e

  let iter_dag' ~iter_ty e f = iter_dag ~iter_ty ~f e

  module type MK = sig
    type 'a with_ctx = ctx -> 'a

    val type_ : t with_ctx
    val eq : (t -> t) with_ctx
    val bool : t with_ctx
    val select : (t -> t) with_ctx
    val var : (var -> t) with_ctx
    val const : (const -> ty list -> t) with_ctx
    val bvar : (int -> ty -> t) with_ctx
    val app : (t -> t -> t) with_ctx
    val lambda_db : (name:string -> ty_v:ty -> t -> t) with_ctx
    val arrow : (t -> t -> t) with_ctx
    val box : (sequent -> t) with_ctx
  end

  let make_ : (module MK) option ref = ref None
end

(* ── Util_chash_: cryptographic hashing ── *)

module Util_chash_ = struct
  module H = Chash

  let rec hash_expr_ (e : expr) : H.t =
    let compute_ e =
      let ctx = H.create () in
      (match e.e_ty with
      | Ty ty -> hasher_expr_ ctx ty
      | _ -> ());
      (match e.e_view with
      | E_var v ->
        H.string ctx "v";
        H.string ctx v.v_name
      | E_const (c, args) ->
        H.string ctx "c";
        H.string ctx c.c_name;
        List.iter (hasher_expr_ ctx) args
      | E_bound_var v ->
        H.string ctx "b";
        H.int ctx v.bv_idx
      | E_app (hd, a) ->
        H.string ctx "@";
        hasher_expr_ ctx hd;
        hasher_expr_ ctx a
      | E_lam (n, _tyv, bod) ->
        H.string ctx "l";
        hasher_expr_ ctx bod
      | E_arrow (a, b) -> H.string ctx ">"
      | E_kind -> H.string ctx "K"
      | E_type -> H.string ctx "T"
      | E_box seq ->
        H.string ctx "[";
        hasher_seq_ ctx seq);
      H.finalize ctx
    in
    if Chash.equal Chash.dummy e.e_hash then (
      let h = compute_ e in
      e.e_hash <- h;
      h
    ) else
      e.e_hash

  and[@inline] hasher_expr_ ctx e =
    let h = hash_expr_ e in
    H.sub ctx h

  and hasher_seq_ ctx (s : sequent) : unit =
    let l =
      List.rev_map hash_expr_ (Expr_set.to_list s.hyps)
      |> List.sort Chash.compare
    in
    H.string ctx "seq";
    List.iter (H.sub ctx) l;
    H.string ctx "|-";
    H.sub ctx (hash_expr_ s.concl)

  let hasher_const_def_ ctx (d : const_def) =
    match d with
    | C_def_expr { vars; rhs } ->
      H.string ctx "def";
      List.iter
        (fun v ->
          H.string ctx v.v_name;
          hasher_expr_ ctx v.v_ty)
        vars;
      H.sub ctx (hash_expr_ rhs)
    | C_def_ty { arity; phi } ->
      H.string ctx "ty";
      H.int ctx arity;
      H.sub ctx (hash_expr_ phi)
    | C_def_ty_abs { arity; phi } ->
      H.string ctx "ty.abs";
      H.int ctx arity;
      H.sub ctx (hash_expr_ phi)
    | C_def_ty_repr { arity; phi } ->
      H.string ctx "ty.repr";
      H.int ctx arity;
      H.sub ctx (hash_expr_ phi)
    | C_def_theory_param { ty_vars; ty } ->
      H.string ctx "param";
      List.iter (fun v -> H.string ctx v.v_name) ty_vars;
      H.sub ctx (hash_expr_ ty)
    | C_def_theory_ty_param { arity } ->
      H.string ctx "ty.param";
      H.int ctx arity
    | C_def_magic magic ->
      H.string ctx "magic";
      H.string ctx magic
    | C_def_skolem { name } ->
      H.string ctx "sk.e";
      H.string ctx name
    | C_def_skolem_ty { name; arity } ->
      H.string ctx "sk.ty";
      H.string ctx name

  let hash_const_def_ ~name (d : const_def) : H.t =
    let ctx = H.create () in
    H.string ctx name;
    hasher_const_def_ ctx d;
    H.finalize ctx
end

(* ── Util_enc_: CBOR encoding ── *)

module Util_enc_ = struct
  open CB.Enc

  let key_expr = make_key (module Expr0)

  let rec enc_var enc (v : var) =
    add_entry enc (list [ text v.v_name; enc_expr enc v.v_ty ])

  and enc_expr enc (e : expr) : ptr =
    let open Expr0 in
    let recurse = enc_expr enc in
    let enc_expr_nonrec enc e =
      match view e with
      | E_kind -> assert false
      | E_type -> add_entry enc @@ text "type"
      | E_const (c, []) when String.equal c.c_name id_bool ->
        add_entry enc @@ text "bool"
      | E_const (c, [ a ]) when String.equal c.c_name id_select ->
        add_entry enc @@ list [ text "select"; recurse a ]
      | E_const (c, [ a ]) when String.equal c.c_name id_eq ->
        add_entry enc @@ list [ text "="; recurse a ]
      | E_const (c, args) ->
        add_entry enc
        @@ list [ text "c"; enc_const enc c; list (List.map recurse args) ]
      | E_lam (str, ty, body) ->
        add_entry enc @@ list [ text "l"; text str; recurse ty; recurse body ]
      | E_app (f, a) -> add_entry enc @@ list [ text "@"; recurse f; recurse a ]
      | E_arrow (a, b) ->
        add_entry enc @@ list [ text ">"; recurse a; recurse b ]
      | E_var v -> add_entry enc @@ list [ text "v"; enc_var enc v ]
      | E_bound_var v ->
        add_entry enc @@ list [ text "bv"; int v.bv_idx; recurse v.bv_ty ]
      | E_box seq -> add_entry enc @@ list [ text "box"; enc_seq enc seq ]
    in
    memo key_expr enc_expr_nonrec enc e

  and enc_const enc (c : const) : ptr =
    let { c_name; c_concrete; c_args; c_ty; c_labels = _ } = c in
    let args =
      match c_args with
      | C_arity n -> list [ text "ar"; int n ]
      | C_ty_vars l -> list (text "vs" :: List.map (enc_var enc) l)
    in
    add_entry enc
    @@ map
         [
           text "cn", add_entry enc (text c_name);
           text "ty", enc_expr enc c_ty;
           text "_", bool c_concrete;
           text "args", args;
         ]

  and enc_seq enc (seq : sequent) : ptr =
    add_entry enc
    @@ map
         [
           text "concl", enc_expr enc seq.concl;
           ( text "hyps",
             list (seq.hyps |> Expr_set.to_list |> List.rev_map (enc_expr enc))
           );
         ]

  let enc_const_def enc def : ptr =
    let evar = enc_var enc in
    let eexpr = enc_expr enc in
    match def with
    | C_def_magic str -> add_entry enc @@ list [ text "magic"; text str ]
    | C_def_expr { vars; rhs } ->
      add_entry enc @@ list [ text "dt"; list (List.map evar vars); eexpr rhs ]
    | C_def_ty { arity; phi } ->
      add_entry enc @@ list [ text "dty"; int arity; eexpr phi ]
    | C_def_ty_abs { arity; phi } ->
      add_entry enc @@ list [ text "dty.abs"; int arity; eexpr phi ]
    | C_def_ty_repr { arity; phi } ->
      add_entry enc @@ list [ text "dty.repr"; int arity; eexpr phi ]
    | C_def_theory_param { ty_vars; ty } ->
      add_entry enc
      @@ list [ text "th.param"; list (List.map evar ty_vars); eexpr ty ]
    | C_def_theory_ty_param { arity } ->
      add_entry enc @@ list [ text "th.typaram"; int arity ]
    | C_def_skolem { name } -> add_entry enc @@ list [ text "sko"; text name ]
    | C_def_skolem_ty { name; arity } ->
      add_entry enc @@ list [ text "sko.ty"; text name; int arity ]
end

(* ── Util_dec_: CBOR decoding ── *)

module Util_dec_ = struct
  open CB.Dec

  let key_expr : expr key = make_key ()
  let key_const : const key = make_key ()
  let key_const_def : const_def key = make_key ()

  let rec dec_var ctx : var t =
    let* l = list value in
    match l with
    | [ `Text v_name; ty ] ->
      let+ v_ty = apply (dec_expr ctx) ty in
      { v_name; v_ty }
    | _ -> fail "expected var"

  and dec_expr ctx : expr t =
    memo key_expr @@ delay
    @@ fun () ->
    let recurse = dec_expr ctx in

    let (module Mk : Expr0.MK) =
      match !Expr0.make_ with
      | None -> assert false
      | Some m -> m
    in

    let* v = value in
    match v with
    | `Text "type" -> return (Mk.type_ ctx)
    | `Text "bool" -> return (Mk.bool ctx)
    | `Array [ `Text "="; ty ] ->
      let+ ty = apply recurse ty in
      Mk.eq ctx ty
    | `Array [ `Text "select"; ty ] ->
      let+ ty = apply recurse ty in
      Mk.select ctx ty
    | `Array [ `Text "c"; c; args ] ->
      let+ c = apply (dec_const ctx) c and+ args = apply (list recurse) args in
      Mk.const ctx c args
    | `Array [ `Text "l"; `Text name; ty; body ] ->
      let+ ty_v = apply recurse ty and+ body = apply recurse body in
      Mk.lambda_db ctx ~name ~ty_v body
    | `Array [ `Text "@"; f; a ] ->
      let+ f = apply recurse f and+ a = apply recurse a in
      Mk.app ctx f a
    | `Array [ `Text ">"; a; b ] ->
      let+ a = apply recurse a and+ b = apply recurse b in
      Mk.arrow ctx a b
    | `Array [ `Text "v"; v ] ->
      let+ v = apply (dec_var ctx) v in
      Mk.var ctx v
    | `Array [ `Text "bv"; `Int i; ty ] ->
      let+ ty = apply recurse ty in
      Mk.bvar ctx i ty
    | `Array [ `Text "box"; seq ] ->
      let+ seq = apply (dec_seq ctx) seq in
      Mk.box ctx seq
    | _ ->
      fail (Fmt.asprintf "expected expr, got %s" (CBOR.Simple.to_diagnostic v))

  and dec_const ctx : const t =
    memo key_const
    @@
    let dec_args =
      let* l = list value in
      match l with
      | [ `Text "ar"; `Int n ] -> return @@ C_arity n
      | `Text "vs" :: vs ->
        let+ vs = apply_l (dec_var ctx) vs in
        C_ty_vars vs
      | _ -> fail "expected constant args"
    in

    let+ c_name = field "cn" text
    and+ c_ty = field "ty" (dec_expr ctx)
    and+ c_concrete = field "_" bool
    and+ c_args = field "args" dec_args in
    { c_name; c_ty; c_concrete; c_args; c_labels = [] }

  and dec_seq ctx : sequent t =
    let+ concl = field "concl" (dec_expr ctx)
    and+ hyps = field "hyps" (list (dec_expr ctx)) in
    let hyps = Expr_set.of_list hyps in
    { concl; hyps }

  let dec_const_def ctx : const_def t =
    let dvar = dec_var ctx in
    let dexpr = dec_expr ctx in

    memo key_const_def
    @@ let* l = list value in
       match l with
       | [ `Text "magic"; `Text str ] -> return @@ C_def_magic str
       | [ `Text "dt"; vars; rhs ] ->
         let+ vars = apply (list dvar) vars and+ rhs = apply dexpr rhs in
         C_def_expr { vars; rhs }
       | [ `Text "dty"; `Int arity; phi ] ->
         let+ phi = apply dexpr phi in
         C_def_ty { arity; phi }
       | [ `Text "dty.abs"; `Int arity; phi ] ->
         let+ phi = apply dexpr phi in
         C_def_ty_abs { arity; phi }
       | [ `Text "dty.repr"; `Int arity; phi ] ->
         let+ phi = apply dexpr phi in
         C_def_ty_repr { arity; phi }
       | [ `Text "th.param"; ty_vars; ty ] ->
         let+ ty_vars = apply (list dvar) ty_vars and+ ty = apply dexpr ty in
         C_def_theory_param { ty_vars; ty }
       | [ `Text "th.typaram"; `Int arity ] ->
         return @@ C_def_theory_ty_param { arity }
       | [ `Text "sko"; `Text name ] -> return @@ C_def_skolem { name }
       | [ `Text "sko.ty"; `Text name; `Int arity ] ->
         return @@ C_def_skolem_ty { name; arity }
       | _ -> fail "expected const_def"
end

(* ── Expr module ── *)

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
    iter e ~f:(fun b x -> if f b x then raise_notrace E_exit);
    false
  with E_exit -> true

let[@inline] for_all ~f e : bool =
  try
    iter e ~f:(fun b x -> if not (f b x) then raise_notrace E_exit);
    true
  with E_exit -> false

let[@inline] is_closed e : bool = db_depth e == 0

let compute_db_depth_ e : int =
  let d1 =
    match ty e with
    | None -> 0
    | Some d -> db_depth d
  in
  let d2 =
    match view e with
    | E_kind | E_type | E_const _ | E_var _ | E_box _ -> 0
    | E_bound_var v -> v.bv_idx + 1
    | E_app (a, b) | E_arrow (a, b) -> max (db_depth a) (db_depth b)
    | E_lam (_, ty, bod) -> max (db_depth ty) (max 0 (db_depth bod - 1))
  in
  max d1 d2

let compute_has_fvars_ e : bool =
  (match ty e with
  | None -> false
  | Some ty -> has_fvars ty)
  ||
  match view e with
  | E_var _ -> true
  | E_box _ | E_kind | E_type | E_bound_var _ -> false
  | E_const (_, args) -> List.exists has_fvars args
  | E_app (a, b) | E_arrow (a, b) -> has_fvars a || has_fvars b
  | E_lam (_, ty, bod) -> has_fvars ty || has_fvars bod

let make_ (ctx : ctx) view ty : t =
  let e =
    { e_view = view; e_ty = ty; e_id = -1; e_flags = 0; e_hash = Chash.dummy }
  in
  let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
  if e == e_h then (
    assert (ctx.ctx_uid land ctx_id_mask == ctx.ctx_uid);
    let has_fvars = compute_has_fvars_ e in
    e_h.e_flags <-
      (compute_db_depth_ e lsl (1 + ctx_id_bits))
      lor (if has_fvars then
             1 lsl ctx_id_bits
           else
             0)
      lor ctx.ctx_uid;
    ctx_check_e_uid ctx e_h
  );
  e_h

let enc = Util_enc_.enc_expr
let dec = Util_dec_.dec_expr
let kind ctx = Lazy.force ctx.ctx_kind
let type_ ctx = Lazy.force ctx.ctx_type

let[@inline] is_eq_to_type e =
  match view e with
  | E_type -> true
  | _ -> false

let[@inline] is_a_type e = is_eq_to_type (ty_exn e)

let is_eq_to_bool e =
  match view e with
  | E_const (c, []) -> String.equal c.c_name id_bool
  | _ -> false

let[@inline] is_a_bool e = is_eq_to_bool (ty_exn e)

let[@inline] is_arrow e =
  match view e with
  | E_arrow _ -> true
  | _ -> false

let[@inline] is_lam e =
  match view e with
  | E_lam _ -> true
  | _ -> false

let[@inline] is_error e =
  match e.e_ty with Ill_typed _ -> true | _ -> false

let mk_error ctx msg : t =
  make_ ctx E_kind (Ill_typed msg)
let bool ctx = Lazy.force ctx.ctx_bool

let var ctx v : t =
  ctx_check_e_uid ctx v.v_ty;
  make_ ctx (E_var v) (Ty v.v_ty)

let var_name ctx s ty : t = var ctx { v_name = s; v_ty = ty }

let bvar ctx i ty : t =
  assert (i >= 0);
  ctx_check_e_uid ctx ty;
  make_ ctx (E_bound_var { bv_idx = i; bv_ty = ty }) (Ty ty)

let[@inline] map ctx ~f (e : t) : t =
  match view e with
  | E_kind | E_type | E_const (_, []) | E_box _ -> e
  | _ ->
    let ty' =
      (match e.e_ty with
      | Ty ty -> Ty (f false ty)
      | Kind -> Kind
      | Ill_typed msg -> Ill_typed msg)
    in
    (match view e with
    | E_var v ->
      let v_ty = f false v.v_ty in
      if v_ty == v.v_ty then
        e
      else
        make_ ctx (E_var { v with v_ty }) ty'
    | E_const (c, args) ->
      let args' = List.map (f false) args in
      if List.for_all2 equal args args' then
        e
      else
        make_ ctx (E_const (c, args')) ty'
    | E_bound_var v ->
      let ty' = f false v.bv_ty in
      if v.bv_ty == ty' then
        e
      else
        make_ ctx
          (E_bound_var { v with bv_ty = ty' })
          (Ty ty')
    | E_app (hd, a) ->
      let hd' = f false hd in
      let a' = f false a in
      if a == a' && hd == hd' then
        e
      else
        make_ ctx (E_app (f false hd, f false a)) ty'
    | E_lam (n, tyv, bod) ->
      let tyv' = f false tyv in
      let bod' = f true bod in
      if tyv == tyv' && bod == bod' then
        e
      else
        make_ ctx (E_lam (n, tyv', bod')) ty'
    | E_arrow (a, b) ->
      let a' = f false a in
      let b' = f false b in
      if a == a' && b == b' then
        e
      else
        make_ ctx (E_arrow (a', b')) ty'
    | E_kind | E_type | E_box _ -> assert false)

exception IsSub

let contains e ~sub : bool =
  let rec aux e =
    if equal e sub then raise_notrace IsSub;
    iter e ~f:(fun _ u -> aux u)
  in
  try
    aux e;
    false
  with IsSub -> true

let free_vars_iter e : var Iter.t =
 fun yield ->
  let rec aux e =
    match view e with
    | E_var v ->
      yield v;
      aux (Var.ty v)
    | E_const (_, args) -> List.iter aux args
    | _ -> iter e ~f:(fun _ u -> aux u)
  in
  aux e

let free_vars ?(init = Var.Set.empty) e : Var.Set.t =
  let set = ref init in
  free_vars_iter e (fun v -> set := Var.Set.add v !set);
  !set

let id_gen_ = ref 0

let mk_const_ ctx c args ty : t = make_ ctx (E_const (c, args)) ty
let subst_empty_ : subst = { ty = Var.Map.empty; m = Var.Map.empty }

let subst_pp_ out (self : subst) : unit =
  if Var.Map.is_empty self.m && Var.Map.is_empty self.ty then
    Fmt.string out "{}"
  else (
    let pp_b out (v, t) =
      Fmt.fprintf out "(@[%a := %a@])" Var.pp_with_ty v expr_pp_ t
    in
    Fmt.fprintf out "@[<hv>{@,%a@,}@]" (pp_iter ~sep:" " pp_b)
      (Iter.append (Var.Map.to_iter self.ty) (Var.Map.to_iter self.m))
  )

let subst_bind_ (subst : subst) v t : subst =
  if is_eq_to_type v.v_ty then
    { subst with ty = Var.Map.add v t subst.ty }
  else
    { subst with m = Var.Map.add v t subst.m }

let db_shift ctx (e : t) (n : int) =
  ctx_check_e_uid ctx e;
  assert (match e.e_ty with Ty t -> is_closed t | _ -> true);
  let rec loop e k : t =
    if is_closed e then
      e
    else if is_a_type e then
      e
    else (
      match view e with
      | E_bound_var bv ->
        if bv.bv_idx >= k then
          bvar ctx (bv.bv_idx + n) bv.bv_ty
        else
          bvar ctx bv.bv_idx bv.bv_ty
      | _ ->
        map ctx e ~f:(fun inbind u ->
            loop u
              (if inbind then
                 k + 1
               else
                 k))
    )
  in
  assert (n >= 0);
  if n = 0 then
    e
  else
    loop e 0

module E_int_tbl = CCHashtbl.Make (struct
  type t = expr * int

  let equal (t1, k1) (t2, k2) = equal t1 t2 && k1 == k2
  let hash (t, k) = H.combine3 27 (hash t) (H.int k)
end)

let subst_ ctx ~recursive e0 (subst : subst) : t =
  let cache_ = E_int_tbl.create 16 in
  let ty_subst_empty_ = Var.Map.is_empty subst.ty in

  let rec loop k e =
    if is_a_type e then
      if ty_subst_empty_ then
        e
      else (
        try E_int_tbl.find cache_ (e, 0)
        with Not_found ->
          let r = loop_uncached_ 0 e in
          E_int_tbl.add cache_ (e, 0) r;
          r
      )
    else (
      try E_int_tbl.find cache_ (e, k)
      with Not_found ->
        let r = loop_uncached_ k e in
        E_int_tbl.add cache_ (e, k) r;
        r
    )
  and loop_uncached_ k (e : t) : t =
    match view e with
    | _ when not (has_fvars e) -> e
    | E_var v when is_eq_to_type v.v_ty ->
      (match Var.Map.find v subst.ty with
      | u ->
        assert (is_closed u);
        if recursive then
          loop 0 u
        else
          u
      | exception Not_found -> var ctx v)
    | E_var v ->
      let v = { v with v_ty = loop k v.v_ty } in
      (match Var.Map.find v subst.m with
      | u ->
        let u = db_shift ctx u k in
        if recursive then
          loop 0 u
        else
          u
      | exception Not_found -> var ctx v)
    | E_const (_, []) -> e
    | _ ->
      map ctx e ~f:(fun inb u ->
          loop
            (if inb then
               k + 1
             else
               k)
            u)
  in

  if Var.Map.is_empty subst.m && Var.Map.is_empty subst.ty then
    e0
  else
    loop 0 e0

let[@inline] subst ctx ~recursive e subst = subst_ ctx ~recursive e subst

let const ctx c args : t =
  ctx_check_e_uid ctx c.c_ty;
  let ty =
    match c.c_args with
    | C_arity n ->
      if List.length args <> n then
        Error.failf (fun k ->
            k "constant %s requires %d arguments, but is applied to %d"
              c.c_name n (List.length args));
      Ty c.c_ty
    | C_ty_vars ty_vars ->
      if List.length args <> List.length ty_vars then
        Error.failf (fun k ->
            k "constant %s requires %d arguments, but is applied to %d"
              c.c_name (List.length ty_vars) (List.length args));
      let sigma = List.fold_left2 subst_bind_ subst_empty_ ty_vars args in
      Ty (subst ~recursive:false ctx c.c_ty sigma)
  in
  mk_const_ ctx c args ty

let eq ctx ty =
  let eq = Lazy.force ctx.ctx_eq_c in
  const ctx eq [ ty ]

let select ctx ty =
  let sel = Lazy.force ctx.ctx_select_c in
  const ctx sel [ ty ]

let abs_on_ ctx (v : var) (e : t) : t =
  ctx_check_e_uid ctx v.v_ty;
  ctx_check_e_uid ctx e;
  if not (is_closed v.v_ty) then
    Error.failf (fun k ->
        k "cannot abstract on variable with non closed type %a" pp v.v_ty);
  let db0 = bvar ctx 0 v.v_ty in
  let body = db_shift ctx e 1 in
  subst ~recursive:false ctx body
    { m = Var.Map.singleton v db0; ty = Var.Map.empty }

let subst_db_0 ctx e ~by:u : t =
  ctx_check_e_uid ctx e;
  ctx_check_e_uid ctx u;

  let cache_ = E_int_tbl.create 8 in

  let rec aux e k : t =
    if is_a_type e then
      e
    else if db_depth e < k then
      e
    else (
      match view e with
      | E_const _ -> e
      | E_bound_var bv when bv.bv_idx = k ->
        db_shift ctx u k
      | _ ->
        (try E_int_tbl.find cache_ (e, k)
         with Not_found ->
           let r =
             map ctx e ~f:(fun inb u ->
                 aux u
                   (if inb then
                      k + 1
                    else
                      k))
           in
           E_int_tbl.add cache_ (e, k) r;
           r)
    )
  in
  if is_closed e then
    e
  else
    aux e 0

let pick_name_ (name0 : string) (e : t) : string =
  let rec loop i =
    let name =
      if i = 0 then
        name0
      else
        Printf.sprintf "%s%d" name0 i
    in
    if free_vars_iter e |> Iter.exists (fun v -> v.v_name = name) then
      loop (i + 1)
    else
      name
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

let open_lambda_exn ctx e =
  match open_lambda ctx e with
  | Some tup -> tup
  | None ->
    Error.failf (fun k -> k "open-lambda: term is not a lambda:@ %a" pp e)

let arrow ctx a b : t =
  if (not (is_a_type a)) || not (is_a_type b) then
    Error.failf (fun k -> k "arrow: both arguments must be types");
  let ty = Ty (type_ ctx) in
  make_ ctx (E_arrow (a, b)) ty

let app ctx f a : t =
  ctx_check_e_uid ctx f;
  ctx_check_e_uid ctx a;

  let ty_f = ty_exn f in
  let ty_a = ty_exn a in

  let[@inline never] fail () =
    Error.failf (fun k ->
        k
          "@[<2>kernel: cannot apply function@ `@[%a@]`@ to argument \
           `@[%a@]`@]@];@ @[function has type@ `@[%a@]`,@ but arg has type \
           `@[%a@]`@]"
          pp f pp a pp ty_f pp ty_a)
  in

  let ty =
    match view ty_f with
    | E_arrow (ty_arg, ty_ret) when equal ty_arg ty_a ->
      ty_ret
    | _ -> fail ()
  in
  let ty = Ty ty in
  let e = make_ ctx (E_app (f, a)) ty in
  e

let app_or_error ctx f a : t =
  match view (ty_exn f) with
  | E_arrow (ty_arg, ty_ret) when equal ty_arg (ty_exn a) ->
    make_ ctx (E_app (f, a)) (Ty ty_ret)
  | _ ->
    mk_error ctx (Fmt.asprintf "cannot apply %a to %a" pp f pp a)

let rec app_l ctx f l =
  match l with
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
  let ty = Ty (bool ctx) in
  make_ ctx (E_box seq) ty

let lambda_db ctx ~name ~ty_v bod : t =
  ctx_check_e_uid ctx ty_v;
  ctx_check_e_uid ctx bod;
  if not (is_a_type ty_v) then
    Error.failf (fun k ->
        k "lambda: variable must have a type as type, not %a" pp ty_v);
  let ty = Ty (arrow ctx ty_v (ty_exn bod)) in
  make_ ctx (E_lam (name, ty_v, bod)) ty

let lambda_or_error ctx v bod =
  try
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~name:v.v_name ~ty_v:v.v_ty bod
  with Error.E _ ->
    mk_error ctx (Fmt.asprintf "lambda_or_error")

let lambda ctx v bod =
  let bod = abs_on_ ctx v bod in
  lambda_db ctx ~name:v.v_name ~ty_v:v.v_ty bod

let lambda_l ctx = CCList.fold_right (lambda ctx)

let () =
  let module M = struct
    type 'a with_ctx = ctx -> 'a

    let type_ = type_
    let bool = bool
    let select = select
    let eq = eq
    let lambda_db = lambda_db
    let box = box
    let arrow = arrow
    let app = app
    let var = var
    let const = const
    let bvar = bvar
    let mk_error = mk_error
  end in
  Expr0.make_ := Some (module M)

let unfold_app = unfold_app

let[@inline] unfold_eq e =
  let f, l = unfold_app e in
  match view f, l with
  | E_const ({ c_name; _ }, [ _ ]), [ a; b ]
    when String.equal c_name id_eq ->
    Some (a, b)
  | _ -> None

let[@unroll 1] rec unfold_arrow e =
  match view e with
  | E_arrow (a, b) ->
    let args, ret = unfold_arrow b in
    a :: args, ret
  | _ -> [], e

let[@unroll 1] rec return_ty e =
  match view e with
  | E_arrow (_, b) -> return_ty b
  | _ -> e

let[@inline] as_const e =
  match e.e_view with
  | E_const (c, args) -> Some (c, args)
  | _ -> None

let[@inline] as_const_exn e =
  match e.e_view with
  | E_const (c, args) -> c, args
  | _ -> Error.failf (fun k -> k "%a is not a constant" pp e)
